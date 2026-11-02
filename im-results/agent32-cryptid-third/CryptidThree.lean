import Lean.Elab.Tactic.Omega
import CryptidSix

set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- Universal E boundary with only a three-one requirement on its right. -/
def eThree (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs m ++ [true,true], false,
    [true,true,true] ++ ys, 4⟩

def packetThree : List Bool := [false,true,false,true,false]

theorem eThree_front (m : Nat) (ys : List Bool) :
  run 16 (eThree m ys) = sweepB m (packetThree ++ ys) := by
  simp [eThree, sweepB, packetThree, run, step, goL, goR, pairs]

theorem eThree_run (m : Nat) (ys : List Bool) :
  run (2*m+19) (eThree m ys) =
    ⟨[], false, List.replicate (2*m+3) true ++ (packetThree ++ ys), 5⟩ := by
  have ht : 2*m+19 = 16+(2*m+3) := by omega
  rw [ht, run_add, eThree_front, sweepB_run]

/-- Exact F return from 0 111 followed by an arbitrary suffix, all k. -/
theorem full_E_three (k : Nat) (ys : List Bool) :
  run (12*k*k+49*k+58)
    (init (List.replicate (3*k+2) true ++
      false :: ([true,true,true] ++ ys))) =
    ⟨[], false, List.replicate (8*k+9) true ++
      (packetThree ++ ys), 5⟩ := by
  have ht : 12*k*k+49*k+58 =
    (12*k*k+41*k+33)+(2*(4*k+3)+19) := by omega
  rw [ht, run_add, prefix_E]
  change run (2*(4*k+3)+19) (eThree (4*k+3) ys) = _
  rw [eThree_run]
  rw [show 2*(4*k+3)+3 = 8*k+9 by omega]

#print axioms eThree_front
#print axioms eThree_run
#print axioms full_E_three
end CryptidBoundary
