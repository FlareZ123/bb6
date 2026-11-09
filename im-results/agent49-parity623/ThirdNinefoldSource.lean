import Agent8BinarySafeSource

/-!
A third, exact neutral ninefold B-drain contraction and a three-letter family
of provably successful original Cryptids #623 synthetic section states.
The new residue is 8 (mod 9), distinct from existing 0 and 6 contractions.
No blank-root reachability or BB(6) outcome is claimed.
-/
namespace BB6.Agent49ThirdNinefoldSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49FlatDrainSource
open BB6.Agent8SafeBudgetSource

/-- An unconditional third neutral residue for the *complete* original B-drain.
In particular this equality includes all failing cases. -/
theorem drain_nine_eight (a b d : Nat) :
    drainB a (9*b+8) d = drainB a b (d+24*b+26) := by
  have heq : 9*b+8=3*(3*b+2)+2 := by omega
  rw [heq]
  by_cases ha : a=0
  · subst a
    rw [drain_three_two_zero (3*b+2) d]
    rw [drain_three_two_zero b (d+6*(3*b+2)+7)]
    congr 1 <;> omega
  · have hapos : 0<a := by omega
    rw [drain_three_two a (3*b+2) d hapos]
    have hrep : 3*b+2+1=3*(b+1) := by omega
    rw [hrep, drain_three (a-1) (b+1) (d+6*(3*b+2)+5) (by omega)]
    have ha1 : a-1+1=a := by omega
    have hb1 : b+1-1=b := by omega
    rw [ha1,hb1]
    congr 1 <;> omega

/-- The three ninefold-neutral digits 0, 6, and 8. -/
inductive Digit where
  | zero | six | eight
  deriving DecidableEq

def ternaryBlock : List Digit → Nat
  | [] => 6
  | .zero :: w => 9*ternaryBlock w
  | .six :: w => 9*ternaryBlock w+6
  | .eight :: w => 9*ternaryBlock w+8

def ternaryCharge : List Digit → Nat
  | [] => 4
  | .zero :: w => ternaryCharge w+2
  | .six :: w => ternaryCharge w+4
  | .eight :: w => ternaryCharge w+2

theorem ternaryBlock_positive (w : List Digit) : 0 < ternaryBlock w := by
  induction w with
  | nil => decide
  | cons bit w ih => cases bit <;> simp only [ternaryBlock] <;> omega

theorem ternaryBlock_even (w : List Digit) : ternaryBlock w%2=0 := by
  induction w with
  | nil => decide
  | cons bit w ih => cases bit <;> simp only [ternaryBlock] <;> omega

theorem ternaryBlock_six (w : List Digit) : 6 ≤ ternaryBlock w := by
  cases w with
  | nil => decide
  | cons bit w =>
    have hp := ternaryBlock_positive w
    cases bit <;> simp only [ternaryBlock] <;> omega

theorem ternaryCharge_even (w : List Digit) : ternaryCharge w%2=0 := by
  induction w with
  | nil => decide
  | cons bit w ih => cases bit <;> simp only [ternaryCharge] <;> omega

/-- Distinct finite words encode distinct positive even block counts. -/
theorem ternaryBlock_injective : ∀ x y : List Digit,
    ternaryBlock x=ternaryBlock y → x=y := by
  intro x
  induction x with
  | nil =>
    intro y h
    cases y with
    | nil => rfl
    | cons bit w =>
      cases bit <;> simp only [ternaryBlock] at h
      all_goals have hp := ternaryBlock_positive w
      all_goals omega
  | cons bit x ih =>
    intro y h
    cases y with
    | nil =>
      cases bit <;> simp only [ternaryBlock] at h
      all_goals have hp := ternaryBlock_positive x
      all_goals omega
    | cons bit' y =>
      cases bit <;> cases bit' <;> simp only [ternaryBlock] at h ⊢
      all_goals first
        | have he : ternaryBlock x = ternaryBlock y := by omega
          cases ih y he
          rfl
        | omega

/-- Exact all-word successful drain, with an explicit full output. -/
theorem ternaryBlock_drain (a : Nat) (w : List Digit) (d : Nat) :
    drainB a (ternaryBlock w) d =
      some (.D a (d+3*ternaryBlock w+ternaryCharge w)) := by
  induction w generalizing d with
  | nil =>
    simp only [ternaryBlock, ternaryCharge]
    have h : drainB 0 6 d = drainB 0 0 (d+22) := by
      simpa only [Nat.zero_mul, Nat.zero_add] using
        (drainB_nine_pump a 0 d)
    rw [h]
    simp [drainB]
  | cons bit w ih =>
    cases bit with
    | zero =>
      simp only [ternaryBlock,ternaryCharge]
      rw [drainB_nine_zero a (ternaryBlock w) d (ternaryBlock_positive w), ih]
      simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
      omega
    | six =>
      simp only [ternaryBlock,ternaryCharge]
      rw [drainB_nine_pump, ih]
      simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
      omega
    | eight =>
      simp only [ternaryBlock,ternaryCharge]
      rw [drain_nine_eight, ih]
      simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
      omega

/-- Each of the 3^n distinct length-n codes gives a successful synthetic
two-section escape in the original high-level map. -/
theorem ternaryBlock_diagonal_escape (w : List Digit) :
    let b := ternaryBlock w
    (highLevelNext (.D b (b-2))).bind highLevelNext =
      some (.D (2+3*b+ternaryCharge w) 7) := by
  intro b
  have hb : 6≤b := ternaryBlock_six w
  have he : b%2=0 := ternaryBlock_even w
  have hdiag : b=b-2+2 := by omega
  have hz : b≠0 := by omega
  have h1 : ¬ ((b-2)%2=1 ∧ b≥b-2+5) := by omega
  have h2 : ¬ ((b-2)%2=0 ∧ b≥b-2+3) := by omega
  have hpar : b%2≠1 := by omega
  have hstep : highLevelNext (.D b (b-2)) = drainB 0 b 2 := by
    simp only [highLevelNext,if_neg hz,if_neg h1,if_neg h2,if_neg hpar,if_pos hdiag]
  rw [hstep]
  have hp : drainB 0 b 2 =
      some (.D 0 (2+3*b+ternaryCharge w)) := by
    dsimp [b]
    exact ternaryBlock_drain 0 w 2
  rw [hp]
  have hs : (2+3*b+ternaryCharge w)%2=0 := by
    have hc := ternaryCharge_even w
    omega
  simp [highLevelNext,hs]


/-- Apply an arbitrary finite neutral-residue word to any positive input block
count; the initial block may be halting or surviving. -/
def embedBlock (w : List Digit) (b : Nat) : Nat :=
  match w with
  | [] => b
  | .zero :: t => 9*embedBlock t b
  | .six :: t => 9*embedBlock t b+6
  | .eight :: t => 9*embedBlock t b+8

def embedCharge : List Digit → Nat
  | [] => 0
  | .zero :: t => embedCharge t+2
  | .six :: t => embedCharge t+4
  | .eight :: t => embedCharge t+2

theorem embedBlock_ge (w : List Digit) (b : Nat) (hb : 0<b) :
    b ≤ embedBlock w b := by
  induction w with
  | nil => simp [embedBlock]
  | cons bit w ih =>
    cases bit <;> simp only [embedBlock] <;> omega

theorem embedBlock_positive (w : List Digit) (b : Nat) (hb : 0<b) :
    0 < embedBlock w b := by
  have h := embedBlock_ge w b hb
  omega

/-- All three neutral symbols commute with the original drain for every
initial first counter, and propagate successes and failures exactly. -/
theorem embed_ninefold (w : List Digit) (a b d : Nat) (hb : 0<b) :
    drainB a (embedBlock w b) d =
      drainB a b (d+3*(embedBlock w b-b)+embedCharge w) := by
  induction w generalizing d with
  | nil => simp [embedBlock,embedCharge]
  | cons bit w ih =>
    have hp := embedBlock_ge w b hb
    have hz := embedBlock_positive w b hb
    cases bit with
    | zero =>
      simp only [embedBlock,embedCharge]
      rw [drainB_nine_zero a (embedBlock w b) d hz, ih]
      congr 1 <;> omega
    | six =>
      simp only [embedBlock,embedCharge]
      rw [drainB_nine_pump, ih]
      congr 1 <;> omega
    | eight =>
      simp only [embedBlock,embedCharge]
      rw [drain_nine_eight, ih]
      congr 1 <;> omega

#print axioms embed_ninefold
#print axioms drain_nine_eight
#print axioms ternaryBlock_injective
#print axioms ternaryBlock_drain
#print axioms ternaryBlock_diagonal_escape
end BB6.Agent49ThirdNinefoldSource
