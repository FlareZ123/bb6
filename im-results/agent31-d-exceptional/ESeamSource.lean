import Lean.Elab.Tactic.Omega
import Boundary

set_option maxHeartbeats 2000000
namespace BB6.ESeamOriginal
open CryptidBoundary

def markedStack : Nat → List Bool
  | 0 => [true]
  | m+1 => false :: true :: markedStack m

/-- Original source C1,D0 2-step pump, all arbitrary untouched right tails. -/
private theorem source_two_step (m : Nat) (ys : List Bool) :
    run 2 (⟨markedStack (m+1), true, ys, 2⟩ : Cfg) =
      ⟨markedStack m, true, [true,true] ++ ys, 2⟩ := by
  simp [run, step, goL, markedStack]

/-- Exact original-source C/D sweep when the first untouched terminal 11
    marker is entered as C/1; output has physically empty left tape. -/
theorem original_marker_sweep (m : Nat) (ys : List Bool) :
    run (2*m+2) (⟨markedStack m, true, ys, 2⟩ : Cfg) =
      ⟨[], false, List.replicate (2*m+2) true ++ ys, 5⟩ := by
  induction m generalizing ys with
  | zero => simp [run, step, goL, markedStack]
  | succ m ih =>
    have ht : 2*(m+1)+2 = 2 + (2*m+2) := by omega
    rw [ht, run_add, source_two_step, ih]
    congr 1
    calc
      List.replicate (2*m+2) true ++ ([true,true] ++ ys) =
          (List.replicate (2*m+2) true ++ List.replicate 2 true) ++ ys := by
            simp only [List.replicate_succ, List.replicate_zero,
              List.cons_append, List.append_assoc]
      _ = List.replicate ((2*m+2)+2) true ++ ys := by
            rw [List.replicate_append_replicate]
      _ = List.replicate (2+(2*m+2)) true ++ ys := by
            rw [show (2*m+2)+2 = 2+(2*m+2) by omega]

#print axioms source_two_step
#print axioms original_marker_sweep
end BB6.ESeamOriginal
