import Lean.Elab.Tactic.Omega
import Boundary

set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- Six initial ones followed by a zero at the E boundary. -/
def eSix (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs m ++ [true,true], false,
    List.replicate 6 true ++ (false::ys), 4⟩

def sweepB (m : Nat) (ys : List Bool) : Cfg :=
  ⟨pairs m ++ [true,true], false, ys, 1⟩

def packetSix : List Bool :=
  [false,true,false,true,false,true,true,true,false]

/-- Six-one E gate reduces in a bounded number of raw steps to the same
    sweep as the original D gate, with a B-on-zero scanning state. -/
theorem eSix_front (m : Nat) (ys : List Bool) :
  run 16 (eSix m ys) = sweepB m (packetSix ++ ys) := by
  simp [eSix, sweepB, packetSix, run, step, goL, goR, pairs, List.append_assoc]

theorem sweepB_run (m : Nat) (ys : List Bool) :
  run (2*m+3) (sweepB m ys) =
    ⟨[], false, List.replicate (2*m+3) true ++ ys, 5⟩ := by
  have hstep : step (sweepB m ys) = step (sweepD m ys) := by
    simp [sweepB, sweepD, step, goL]
  calc
    run (2*m+3) (sweepB m ys) = run (2*m+3) (sweepD m ys) := by
      have ht : 2*m+3 = (2*m+2)+1 := by omega
      rw [ht]
      simp only [run]
      rw [hstep]
    _ = _ := sweepD_run m ys

/-- Every E boundary of this form returns to F on blank after an exact
    linearly sized primitive run, preserving all unknown trailing bits. -/
theorem eSix_run (m : Nat) (ys : List Bool) :
  run (2*m+19) (eSix m ys) =
    ⟨[], false, List.replicate (2*m+3) true ++
      (packetSix ++ ys), 5⟩ := by
  have ht : 2*m+19 = 16+(2*m+3) := by omega
  rw [ht, run_add, eSix_front, sweepB_run]

/-- A complete source-level raw Turing machine F-return in the previously
    unresolved six-one E branch, all k and arbitrary finite suffix. -/
theorem full_E_six (k : Nat) (ys : List Bool) :
  run (12*k*k+49*k+58)
    (init (List.replicate (3*k+2) true ++
      false :: (List.replicate 6 true ++ (false::ys)))) =
    ⟨[], false, List.replicate (8*k+9) true ++ (packetSix ++ ys), 5⟩ := by
  have ht : 12*k*k+49*k+58 =
    (12*k*k+41*k+33)+(2*(4*k+3)+19) := by omega
  rw [ht, run_add, prefix_E]
  change run (2*(4*k+3)+19) (eSix (4*k+3) ys) = _
  rw [eSix_run]
  rw [show 2*(4*k+3)+3 = 8*k+9 by omega]

#print axioms eSix_front
#print axioms sweepB_run
#print axioms eSix_run
#print axioms full_E_six
end CryptidBoundary
