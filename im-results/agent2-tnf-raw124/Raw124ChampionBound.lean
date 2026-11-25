import CostRecurrence
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2Raw124ChampionBound

open BB6ChampionArithmetic

private theorem nat_le_two_pow_local (b : Nat) : b ≤ 2^b := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hp : 0 < 2^b := Nat.pow_pos (by decide)
      calc
        b+1 ≤ 2^b+1 := Nat.succ_le_succ ih
        _ ≤ 2^b+2^b := by omega
        _ = 2^(b+1) := by simp [Nat.pow_succ, Nat.mul_two]

/-- Every proposed increment cost dominates its leading six-times-four-power
term. The Nat subtraction by 9*b is harmless because 9*b ≤ 42*2^b. -/
theorem proposedIncrementCost_ge_six_four (m n a b : Nat) :
    6*4^b ≤ proposedIncrementCost m n a b := by
  have hb : b ≤ 2^b := nat_le_two_pow_local b
  have h9 : 9*b ≤ 42*2^b := by omega
  unfold proposedIncrementCost
  omega

/-- Any nonempty section includes at least its first proposed increment. -/
theorem sectionResult_cost_ge_six_four (n m a b : Nat) (hn : 0<n) :
    6*4^b ≤ (sectionResult n m a b).cost := by
  cases n with
  | zero => omega
  | succ n =>
      simp only [sectionResult]
      have h := proposedIncrementCost_ge_six_four (m%3) (n+1) a b
      omega

/-- A tiny, symbolic lower bound on the exact champion score expression.
The first section alone contributes at least 6*4^63 successful steps. -/
theorem proposedChampionScore_ge_two_million :
    2_000_000 ≤ proposedTM63Moves+7 := by
  have hfirst :
      6*4^63 ≤ (sectionResult 7 2 6 63).cost :=
    sectionResult_cost_ge_six_four 7 2 6 63 (by omega)
  have hpow : 2_000_000 ≤ 6*4^63 := by decide
  calc
    2_000_000 ≤ 6*4^63 := hpow
    _ ≤ (sectionResult 7 2 6 63).cost := hfirst
    _ ≤ proposedTM63Moves+7 := by
      unfold proposedTM63Moves
      omega

#print axioms proposedIncrementCost_ge_six_four
#print axioms sectionResult_cost_ge_six_four
#print axioms proposedChampionScore_ge_two_million

end BB6.Agent2Raw124ChampionBound
