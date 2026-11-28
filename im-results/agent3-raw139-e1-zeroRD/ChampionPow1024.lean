import CostRecurrence
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ChampionPow1024

open BB6ChampionArithmetic

/-!
Uniform-sized symbolic lower bound extracted from the SECOND source-counted
increment of the exact attained champion. The proof never evaluates
4^(2^63-1) or the giant champion score.
-/

private def secondRight : Nat := 2^63-1

/-! A strictly arithmetic score wrapper. Its root equality is the same
definitional arithmetic identity as the independently source-proved TM63
composition, but imports no terminal-machine proof infrastructure. This
theorem bounds the *defined score expression*; attainment is a separate
already-certified input to later consumers. -/
private def scoreFormula (rootSteps L n a b : Nat) : Nat :=
  let f := sectionResult n 2 a b
  let L1 := L + f.exponent + 2
  let N1 := resetIndex L f.exponent
  let g := sectionResult N1 2 f.right (nextRight f.right)
  let L2 := L1 + g.exponent + 2
  let N2 := resetIndex L1 g.exponent
  let j := sectionResult N2 2 g.right (nextRight g.right)
  rootSteps + f.cost + resetCost L f.exponent f.right + g.cost +
    resetCost L1 g.exponent g.right + j.cost + terminalCost L2 j.exponent

private theorem scoreFormula_root :
    scoreFormula 27959 3 7 6 63 = proposedTM63Moves := by
  rfl

private theorem firstCost_le_formula (rootSteps L n a b : Nat) :
    (sectionResult n 2 a b).cost ≤ scoreFormula rootSteps L n a b := by
  dsimp [scoreFormula]
  omega

private theorem first_cost_le_proposed_score :
    (sectionResult 7 2 6 63).cost ≤ proposedTM63Moves + 7 := by
  have h : (sectionResult 7 2 6 63).cost ≤
      scoreFormula 27959 3 7 6 63 + 7 :=
    Nat.le_trans (firstCost_le_formula 27959 3 7 6 63)
      (Nat.le_add_right _ _)
  exact Eq.mp
    (congrArg (fun n : Nat =>
      (sectionResult 7 2 6 63).cost ≤ n + 7) scoreFormula_root) h

private theorem source_firstCost_le (n m a b : Nat) :
    proposedIncrementCost (m%3) (n+1) a b ≤
      (sectionResult (n+1) m a b).cost := by
  simp only [sectionResult]
  exact Nat.le_add_right _ _

/-- One symbolic section of the arithmetic cost recurrence, with the
    recursive tail left opaque even when the next exponent is enormous. -/
private theorem sectionResult_succ_cost (n m a b : Nat) :
    (sectionResult (n+1) m a b).cost =
      proposedIncrementCost (m%3) (n+1) a b +
      (sectionResult n (nextMarker m) (nextExponent m a b) (nextRight b)).cost := by
  rfl


private theorem second_increment_general (b e : Nat)
    (h64 : 64 ≤ b) (he : e ≤ b) (hsmall : 9*b ≤ 2^128) :
    2^e ≤ proposedIncrementCost 1 6 71 b := by
  have hpow : 2^e ≤ 4^b := by
    calc
      2^e ≤ 4^e := Nat.pow_le_pow_left (by decide) _
      _ ≤ 4^b :=
        Nat.pow_le_pow_right (by decide) he
  have hb : 9*b ≤ 4^b := by
    calc
      9*b ≤ 2^128 := hsmall
      _ = 4^64 := by decide
      _ ≤ 4^b := Nat.pow_le_pow_right (by decide) h64
  unfold proposedIncrementCost
  omega

theorem second_increment_ge_pow1024 :
    2^1024 ≤ proposedIncrementCost 1 6 71 secondRight := by
  exact second_increment_general secondRight 1024
    (by decide) (by decide) (by decide)

/-- Source arithmetic: the second increment is a nonnegative summand of
    the first section. Prove this *for symbolic b*, only then instantiate
    b=63. Instantiating first makes Lean attempt kernel evaluation of
    4^(2^63−1), which is invalid and unnecessary. -/
private theorem second_layer_lower_bound (b : Nat) :
    proposedIncrementCost 1 6 (nextExponent 2 6 b) (nextRight b) ≤
      (sectionResult 7 2 6 b).cost := by
  have hr : proposedIncrementCost 1 6 (nextExponent 2 6 b) (nextRight b) ≤
      (sectionResult 6 1 (nextExponent 2 6 b) (nextRight b)).cost :=
    source_firstCost_le 5 1 _ _
  have hs := sectionResult_succ_cost 6 2 6 b
  have hm : nextMarker 2 = 1 := by decide
  have he : (sectionResult 6 (nextMarker 2) (nextExponent 2 6 b) (nextRight b)).cost =
      (sectionResult 6 1 (nextExponent 2 6 b) (nextRight b)).cost := by
    rw [hm]
  calc
    proposedIncrementCost 1 6 (nextExponent 2 6 b) (nextRight b) ≤
      (sectionResult 6 1 (nextExponent 2 6 b) (nextRight b)).cost := hr
    _ ≤ proposedIncrementCost 2 7 6 b +
      (sectionResult 6 1 (nextExponent 2 6 b) (nextRight b)).cost := Nat.le_add_left _ _
    _ = (sectionResult 7 2 6 b).cost := by
      rw [← he]
      exact hs.symm

theorem second_increment_le_first_section :
    proposedIncrementCost 1 6 71 secondRight ≤
      (sectionResult 7 2 6 63).cost := by
  have he : nextExponent 2 6 63 = 71 := by decide
  have hb : nextRight 63 = secondRight := by decide
  simpa only [he, hb] using second_layer_lower_bound 63

theorem champion_score_ge_pow1024 :
    2^1024 ≤ proposedTM63Moves + 7 := by
  calc
    2^1024 ≤ proposedIncrementCost 1 6 71 secondRight :=
      second_increment_ge_pow1024
    _ ≤ (sectionResult 7 2 6 63).cost :=
      second_increment_le_first_section
    _ ≤ proposedTM63Moves + 7 :=
      first_cost_le_proposed_score

/-- A finite but extremely strong uniform attainment interface:
the exact certified champion score exceeds 2^e for every
e ≤ 2^63−1. No tower is unfolded to establish the inequality. -/
theorem champion_score_ge_pow_of_le (e : Nat) (he : e ≤ 2^63-1) :
    2^e ≤ proposedTM63Moves + 7 := by
  have heb : e ≤ secondRight := by simpa [secondRight] using he
  have hfirst : 2^e ≤ proposedIncrementCost 1 6 71 secondRight :=
    second_increment_general secondRight e (by decide) heb (by decide)
  exact Nat.le_trans (Nat.le_trans hfirst second_increment_le_first_section)
    first_cost_le_proposed_score

theorem champion_score_ge_pow32768 :
    2^32768 ≤ proposedTM63Moves + 7 :=
  champion_score_ge_pow_of_le 32768 (by decide)

#print axioms first_cost_le_proposed_score
#print axioms scoreFormula_root
#print axioms champion_score_ge_pow_of_le
#print axioms champion_score_ge_pow32768

#print axioms second_increment_ge_pow1024
#print axioms second_increment_le_first_section
#print axioms champion_score_ge_pow1024

end BB6.Agent3ChampionPow1024
