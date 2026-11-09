import Agent49ThirdNinefoldSource

/-!
A source-faithful Catalan family of exactly terminating complete B-drains for
the original six-state #623 machine. Each uncoloured Dyck path of 2n steps
has n downward steps, independently coloured by residue one or two, giving
2^n * Catalan(n) distinct explicit successful block counts. All lengths are
quantified and the initial first counter is arbitrary.

This is a synthetic B-input theorem and does NOT decide blank-root BB(6).
-/
namespace BB6.Agent49DyckSafeSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49FlatDrainSource
open BB6.Agent8SafeBudgetSource

/-- The three *inverse* reduction moves: up in the first counter,
down from residue one, and down from residue two. -/
inductive Step where
  | up | one | two
  deriving DecidableEq

/-- Inverse ternary block evaluation. The terminal block is six. -/
def pathBlock : List Step → Nat
  | [] => 6
  | .up :: w => 3*(pathBlock w+1)
  | .one :: w => 3*pathBlock w+1
  | .two :: w => 3*pathBlock w-1

/-- Exact charge beyond three times the block count. -/
def pathCharge : List Step → Nat
  | [] => 4
  | .up :: w => pathCharge w
  | .one :: w => pathCharge w+4
  | .two :: w => pathCharge w+2

theorem pathBlock_ge (w : List Step) : 6≤pathBlock w := by
  induction w with
  | nil => decide
  | cons s w ih => cases s <;> simp only [pathBlock] <;> omega

/-- A walk with nonnegative height from h to k. Its downward constructors
require an existing unit of height. A balanced path is Walk w 0 0. -/
inductive Walk : List Step → Nat → Nat → Prop where
  | nil (h : Nat) : Walk [] h h
  | up {w h k} (hw : Walk w (h+1) k) : Walk (.up :: w) h k
  | one {w h k} (hw : Walk w h k) : Walk (.one :: w) (h+1) k
  | two {w h k} (hw : Walk w h k) : Walk (.two :: w) (h+1) k

/-- Exact original-source B-drain, all naturals and all nonnegative walks:
the first counter changes by precisely the difference of endpoint heights.
For a balanced walk, the first counter is preserved for every starting a. -/
theorem pathDrain (w : List Step) (h k a d : Nat) (hw : Walk w h k) :
    drainB (a+h) (pathBlock w) d =
      some (.D (a+k) (d+3*pathBlock w+pathCharge w)) := by
  induction hw generalizing a d with
  | nil h =>
    simp only [pathBlock,pathCharge]
    have hm : drainB (a+h) 6 d = drainB (a+h) 0 (d+22) := by
      simpa only [Nat.zero_mul,Nat.zero_add] using drainB_nine_pump (a+h) 0 d
    rw [hm]
    simp [drainB]
  | up hw ih =>
    rename_i w0 h0 k0
    simp only [pathBlock,pathCharge]
    rw [drain_three (a+h0) (pathBlock w0+1) d (by omega)]
    have hc : (pathBlock w0+1)-1=pathBlock w0 := by omega
    rw [hc]
    have ha : (a+h0)+1=a+(h0+1) := by omega
    rw [ha, ih]
    simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
    omega
  | one hw ih =>
    rename_i w0 h0 k0
    simp only [pathBlock,pathCharge]
    rw [drain_three_one (a+(h0+1)) (pathBlock w0) d (by omega)]
    have ha : (a+(h0+1))-1=a+h0 := by omega
    rw [ha, ih]
    simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
    omega
  | two hw ih =>
    rename_i w0 h0 k0
    simp only [pathBlock,pathCharge]
    have hp := pathBlock_ge w0
    have hb : 3*pathBlock w0-1=3*(pathBlock w0-1)+2 := by omega
    rw [hb, drain_three_two (a+(h0+1)) (pathBlock w0-1) d (by omega)]
    have hc : (pathBlock w0-1)+1=pathBlock w0 := by omega
    have ha : (a+(h0+1))-1=a+h0 := by omega
    rw [hc,ha,ih]
    simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
    omega

/-- The numeric block code is injective even on arbitrary finite step lists,
therefore also on the coloured Dyck sublanguage. -/
theorem pathBlock_injective : ∀ x y : List Step,
    pathBlock x=pathBlock y → x=y := by
  intro x
  induction x with
  | nil =>
    intro y h
    cases y with
    | nil => rfl
    | cons s w =>
      cases s <;> simp only [pathBlock] at h
      all_goals have hp := pathBlock_ge w
      all_goals omega
  | cons s x ih =>
    intro y h
    cases y with
    | nil =>
      cases s <;> simp only [pathBlock] at h
      all_goals have hp := pathBlock_ge x
      all_goals omega
    | cons t y =>
      cases s <;> cases t <;> simp only [pathBlock] at h ⊢
      all_goals first
        | have he : pathBlock x=pathBlock y := by
            have hx := pathBlock_ge x
            have hy := pathBlock_ge y
            omega
          cases ih y he
          rfl
        | have hx := pathBlock_ge x
          have hy := pathBlock_ge y
          omega

/-- Convenient balanced specialization with zero initial walk height. -/
theorem balanced_drain (w : List Step) (a d : Nat) (hw : Walk w 0 0) :
    drainB a (pathBlock w) d =
      some (.D a (d+3*pathBlock w+pathCharge w)) := by
  simpa using pathDrain w 0 0 a d hw

#print axioms pathDrain
#print axioms pathBlock_injective
#print axioms balanced_drain
end BB6.Agent49DyckSafeSource
