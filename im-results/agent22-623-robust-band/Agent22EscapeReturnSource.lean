import Agent22RobustBandSource
import Agent49FlatDrainSource

/-!
Exact terminal result of the *first* surviving B-drain immediately above
any ternary-ones fatal band. Every such first survivor returns first counter
zero, with a parity-determined and affine third-counter correction.
-/
namespace BB6.Agent22EscapeReturnSource
open BB6Robust
open BB6.Agent49Capacity
open BB6.Agent49FlatDrainSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

private theorem boundary_zero_return (a d : Nat) :
    drainB a (boundary a) d =
      some (.D 0 (d+3*boundary a+4*a)) := by
  induction a generalizing d with
  | zero => simp [boundary,drainB]
  | succ a ih =>
      change drainB (a+1) (3*boundary a+1) d =
        some (.D 0 (d+3*(3*boundary a+1)+4*(a+1)))
      rw [drain_three_one (a+1) (boundary a) d (by omega)]
      have h := ih (d+6*boundary a+7)
      have hdec : a+1-1=a := by omega
      rw [hdec,h]
      simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
      omega

private theorem boundary_plus_return (a d : Nat) :
    drainB a (boundary (a+1)+1) d =
      some (.D 0 (d+3*(boundary (a+1)+1)+2*a+1)) := by
  induction a generalizing d with
  | zero =>
      change drainB 0 (3*0+2) d = some (.D 0 (d+3*2+1))
      rw [drain_three_two_zero]
      simp [drainB]
  | succ a ih =>
      change drainB (a+1) (3*boundary (a+1)+2) d =
        some (.D 0 (d+3*(3*boundary (a+1)+2)+2*(a+1)+1))
      rw [drain_three_two (a+1) (boundary (a+1)) d (by omega)]
      have h := ih (d+6*boundary (a+1)+5)
      have hdec : a+1-1=a := by omega
      rw [hdec,h]
      simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
      omega

/-- At every even surplus r=2k the first surviving B-drain has first
counter zero and sharp additive correction 4a+4k over the 3b budget. -/
theorem first_survivor_even (k a d : Nat) :
    drainB a (boundary (a+2*k)+escape (2*k)) d =
      some (.D 0 (d+3*(boundary (a+2*k)+escape (2*k))+4*a+4*k)) := by
  induction k generalizing a d with
  | zero =>
      simpa only [Nat.mul_zero, Nat.add_zero, escape] using boundary_zero_return a d
  | succ k ih =>
      let q := boundary (a+1+2*k)+escape (2*k)+1
      have hn : a+2*(k+1) = (a+1+2*k)+1 := by omega
      have he : escape (2*(k+1)) = 3*escape (2*k)+2 := by
        have hr : 2*(k+1)=2*k+2 := by omega
        rw [hr]
        rfl
      have hb : boundary (a+2*(k+1))+escape (2*(k+1))=3*q := by
        dsimp [q]
        rw [hn,he,boundary]
        omega
      have hq : 0<q := by dsimp [q]; omega
      have hqred : q-1 = boundary (a+1+2*k)+escape (2*k) := by dsimp [q]
      rw [hb,drain_three a q d hq,hqred]
      have h := ih (a+1) (d+6*q+3)
      rw [h]
      simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
      omega

/-- The odd surplus r=2k+1 has additive correction 2a+2k+1. -/
theorem first_survivor_odd (k a d : Nat) :
    drainB a (boundary (a+2*k+1)+escape (2*k+1)) d =
      some (.D 0 (d+3*(boundary (a+2*k+1)+escape (2*k+1))+2*a+2*k+1)) := by
  induction k generalizing a d with
  | zero =>
      simpa only [Nat.mul_zero, Nat.add_zero, escape] using boundary_plus_return a d
  | succ k ih =>
      let q := boundary (a+1+2*k+1)+escape (2*k+1)+1
      have hn : a+2*(k+1)+1 = (a+1+2*k+1)+1 := by omega
      have he : escape (2*(k+1)+1) = 3*escape (2*k+1)+2 := by
        have hr : 2*(k+1)+1=(2*k+1)+2 := by omega
        rw [hr]
        rfl
      have hb : boundary (a+2*(k+1)+1)+escape (2*(k+1)+1)=3*q := by
        dsimp [q]
        rw [hn,he,boundary]
        omega
      have hq : 0<q := by dsimp [q]; omega
      have hqred : q-1 = boundary (a+1+2*k+1)+escape (2*k+1) := by dsimp [q]
      rw [hb,drain_three a q d hq,hqred]
      have h := ih (a+1) (d+6*q+3)
      rw [h]
      simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
      omega

#print axioms first_survivor_even
#print axioms first_survivor_odd
end BB6.Agent22EscapeReturnSource
