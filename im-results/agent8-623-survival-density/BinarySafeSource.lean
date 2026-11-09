import Agent8SafeBudgetSource

/-!
A binary Cantor family of exponentially many provably successful original
Cryptids #623 B-drain inputs with zero initial first counter. Distinct
finite bitwords map injectively to positive even block counts, and both
digit-carry contractions preserve zero safeBudget.
These are synthetic inputs, not asserted blank-root visits.
-/
namespace BB6.Agent8BinarySafeSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8SafeBudgetSource

def wordBlock : List Bool → Nat
  | [] => 6
  | false :: w => 9*wordBlock w
  | true :: w => 9*wordBlock w+6

def wordCharge : List Bool → Nat
  | [] => 4
  | false :: w => wordCharge w+2
  | true :: w => wordCharge w+4

theorem wordBlock_positive (w : List Bool) : 0 < wordBlock w := by
  induction w with
  | nil => decide
  | cons bit w ih => cases bit <;> simp only [wordBlock] <;> omega

theorem wordBlock_even (w : List Bool) : wordBlock w%2=0 := by
  induction w with
  | nil => decide
  | cons bit w ih => cases bit <;> simp only [wordBlock] <;> omega

theorem wordBlock_six (w : List Bool) : 6 ≤ wordBlock w := by
  have h := wordBlock_positive w
  cases w with
  | nil => decide
  | cons bit w =>
    have hchild := wordBlock_positive w
    cases bit <;> simp only [wordBlock] <;> omega

theorem wordCharge_even (w : List Bool) : wordCharge w%2=0 := by
  induction w with
  | nil => decide
  | cons bit w ih => cases bit <;> simp only [wordCharge] <;> omega

theorem wordBlock_budget_zero (w : List Bool) : safeBudget (wordBlock w)=0 := by
  induction w with
  | nil => decide +kernel
  | cons bit w ih =>
      cases bit with
      | false => simpa only [wordBlock,safeBudget_nine_zero (wordBlock w) (wordBlock_positive w)] using ih
      | true => simpa only [wordBlock,safeBudget_nine_pump (wordBlock w)] using ih

/-- Each binary word encodes a distinct positive safe block count. -/
theorem wordBlock_injective : ∀ x y : List Bool,
    wordBlock x=wordBlock y → x=y := by
  intro x
  induction x with
  | nil =>
    intro y h
    cases y with
    | nil => rfl
    | cons bit w =>
      cases bit <;> simp only [wordBlock] at h
      · omega
      · have hp := wordBlock_positive w
        omega
  | cons bit x ih =>
    intro y h
    cases y with
    | nil =>
      cases bit <;> simp only [wordBlock] at h
      · omega
      · have hp := wordBlock_positive x
        omega
    | cons bit' y =>
      cases bit <;> cases bit' <;> simp only [wordBlock] at h ⊢
      · have he : wordBlock x = wordBlock y := by omega
        cases ih y he
        rfl
      · omega
      · omega
      · have he : wordBlock x = wordBlock y := by omega
        cases ih y he
        rfl

/-- Every finite binary word gives an exact source-original successful
B-drain with a zero first counter and completely explicit output. -/
theorem wordBlock_drain (w : List Bool) (d : Nat) :
  drainB 0 (wordBlock w) d =
    some (.D 0 (d+3*wordBlock w+wordCharge w)) := by
  induction w generalizing d with
  | nil =>
    simp only [wordBlock,wordCharge]
    have h : drainB 0 6 d = drainB 0 0 (d+22) := by
      simpa only [Nat.zero_mul, Nat.zero_add] using
        (drainB_nine_pump 0 0 d)
    rw [h]
    simp [drainB]
  | cons bit w ih =>
      cases bit with
      | false =>
        simp only [wordBlock,wordCharge]
        rw [drainB_nine_zero 0 (wordBlock w) d (wordBlock_positive w), ih]
        simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
        omega
      | true =>
        simp only [wordBlock,wordCharge]
        rw [drainB_nine_pump, ih]
        simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
        omega

/-- Arbitrarily many distinct, explicitly successful two-return
synthetic diagonal sources in the unmodified six-state accelerator. -/
theorem wordBlock_diagonal_escape (w : List Bool) :
    let b := wordBlock w
    (highLevelNext (.D b (b-2))).bind highLevelNext =
      some (.D (2+3*b+wordCharge w) 7) := by
  intro b
  have hb : 6≤b := wordBlock_six w
  have he : b%2=0 := wordBlock_even w
  have hdiag : b=b-2+2 := by omega
  have hz : b≠0 := by omega
  have h1 : ¬ ((b-2)%2=1 ∧ b≥b-2+5) := by omega
  have h2 : ¬ ((b-2)%2=0 ∧ b≥b-2+3) := by omega
  have hpar : b%2≠1 := by omega
  have hstep : highLevelNext (.D b (b-2)) = drainB 0 b 2 := by
    simp only [highLevelNext,if_neg hz,if_neg h1,if_neg h2,if_neg hpar,if_pos hdiag]
  rw [hstep]
  have hp : drainB 0 b 2 =
      some (.D 0 (2+3*b+wordCharge w)) := by
    dsimp [b]
    exact wordBlock_drain w 2
  rw [hp]
  have hs : (2+3*b+wordCharge w)%2=0 := by
    have hc := wordCharge_even w
    omega
  simp [highLevelNext,hs]

#print axioms wordBlock_budget_zero
#print axioms wordBlock_injective
#print axioms wordBlock_drain
#print axioms wordBlock_diagonal_escape
end BB6.Agent8BinarySafeSource
