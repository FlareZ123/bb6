import Lean.Elab.Tactic.Omega
import CryptidSix

set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- A seven-symbol E-boundary cylinder, with arbitrary untouched suffix. -/
def eSeven (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs m ++ [true,true], false,
    [true,false,true,false,true,true,true] ++ ys, 4⟩

def packetSeven : List Bool :=
  [false,true,false,true,false,true,false,true,false]

theorem eSeven_front (m : Nat) (ys : List Bool) :
  run 28 (eSeven m ys) = sweepB m (packetSeven ++ ys) := by
  simp [eSeven, sweepB, packetSeven, run, step, goL, goR, pairs]

theorem eSeven_run (m : Nat) (ys : List Bool) :
  run (2*m+31) (eSeven m ys) =
    ⟨[], false, List.replicate (2*m+3) true ++
      (packetSeven ++ ys), 5⟩ := by
  have ht : 2*m+31 = 28+(2*m+3) := by omega
  rw [ht, run_add, eSeven_front, sweepB_run]

theorem full_E_seven (k : Nat) (ys : List Bool) :
  run (12*k*k+49*k+70)
    (init (List.replicate (3*k+2) true ++
      false :: ([true,false,true,false,true,true,true] ++ ys))) =
    ⟨[], false, List.replicate (8*k+9) true ++
      (packetSeven ++ ys), 5⟩ := by
  have ht : 12*k*k+49*k+70 =
    (12*k*k+41*k+33)+(2*(4*k+3)+31) := by omega
  rw [ht, run_add, prefix_E]
  change run (2*(4*k+3)+31) (eSeven (4*k+3) ys) = _
  rw [eSeven_run]
  rw [show 2*(4*k+3)+3 = 8*k+9 by omega]

#print axioms eSeven_front
#print axioms eSeven_run
#print axioms full_E_seven
end CryptidBoundary
