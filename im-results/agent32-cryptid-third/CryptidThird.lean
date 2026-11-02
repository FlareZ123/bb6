import Lean.Elab.Tactic.Omega
import Boundary

set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- E-boundary after one further zero. Its alternating block contains
    three leading pairs that a fixed 14-step prefix consumes. -/
def preE (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+3) ++ [true,true], false, false::ys, 4⟩

/-- Symbolic, arbitrary-suffix 14-step transfer into the established D sweep. -/
theorem preE_start (m : Nat) (ys : List Bool) :
  run 14 (preE m ys) =
    sweepD m ([true,true,false] ++ List.replicate 6 true ++ ys) := by
  have hp : pairs (m+3) = pairs (3+m) := by rw [Nat.add_comm]
  simp [preE, hp, sweepD, run, step, goL, goR, pairs, List.append_assoc]

/-- Entire E-boundary left sweep. No restriction on the suffix. -/
theorem preE_run (m : Nat) (ys : List Bool) :
  run (2*m+17) (preE m ys) =
    ⟨[], false, List.replicate (2*m+5) true ++
      (false :: List.replicate 6 true ++ ys), 5⟩ := by
  have ht : 2*m+17 = 14+(2*m+3) := by omega
  rw [ht, run_add, preE_start, sweepD_run]
  have hr :
      List.replicate (2*m+3) true ++
        ([true,true,false] ++ List.replicate 6 true ++ ys) =
      List.replicate (2*m+5) true ++
        (false :: List.replicate 6 true ++ ys) := by
    calc
      _ = (List.replicate (2*m+3) true ++ List.replicate 2 true) ++
            (false :: List.replicate 6 true ++ ys) := by
              simp [List.append_assoc]
      _ = List.replicate ((2*m+3)+2) true ++
            (false :: List.replicate 6 true ++ ys) := by
              rw [List.replicate_append_replicate]
      _ = _ := by rw [show (2*m+3)+2=2*m+5 by omega]
  exact congrArg (fun z : List Bool => Cfg.mk [] false z 5) hr

/-- The remaining initial-block congruence class: a universally valid
    raw-step return carrying a fixed six-one packet. -/
theorem full_E_00 (k : Nat) (ys : List Bool) :
  run (12*k*k+49*k+50)
    (init (List.replicate (3*k+2) true ++ false::false::ys)) =
    ⟨[], false, List.replicate (8*k+5) true ++
      (false :: List.replicate 6 true ++ ys), 5⟩ := by
  have ht : 12*k*k+49*k+50 =
      (12*k*k+41*k+33)+(2*(4*k)+17) := by omega
  rw [ht, run_add, prefix_E]
  change run (2*(4*k)+17) (preE (4*k) ys) = _
  rw [preE_run]
  rw [show 2*(4*k)+5 = 8*k+5 by omega]

#print axioms preE_start
#print axioms preE_run
#print axioms full_E_00
end CryptidBoundary
