import Lean.Elab.Tactic.Omega
import Boundary

set_option maxHeartbeats 10000000
set_option maxRecDepth 1024

namespace BB6.Agent32ETriple

open CryptidBoundary

/-- An E input with right prefix 110111, and unrestricted binary tail. -/
def eTripleZero (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false :: false :: pairs (m+3) ++ [true,true], false,
    [true,true,false,true,true,true] ++ ys, 4⟩

def packet : List Bool :=
  [true,true,false] ++ List.replicate 6 true ++
    [false,true,false,true,false]

/-- An exact 32-transition turn into the source-certified D sweep,
    requiring no assumptions on left alternating length or right suffix. -/
theorem eTripleZero_front (m : Nat) (ys : List Bool) :
    run 32 (eTripleZero m ys) = sweepD m (packet ++ ys) := by
  simp [eTripleZero, sweepD, packet, run, step, goL, goR, pairs,
    List.append_assoc]

theorem eTripleZero_run (m : Nat) (ys : List Bool) :
    run (2*m+35) (eTripleZero m ys) =
      ⟨[],false,List.replicate (2*m+3) true ++ (packet ++ ys),5⟩ := by
  have ht : 2*m+35=32+(2*m+3) := by omega
  rw [ht,run_add,eTripleZero_front,sweepD_run]

/-- New universal original-machine F-section return on 0110111. -/
theorem full_E_triple_zero (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,true,false,true,true,true] ++ ys))) =
    ⟨[],false,List.replicate (8*k+3) true ++ (packet ++ ys),5⟩ := by
  have ht : 12*k*k+49*k+68 =
      (12*k*k+41*k+33)+(2*(4*k)+35) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k)+35) (eTripleZero (4*k) ys) = _
  rw [eTripleZero_run]
  rw [show 2*(4*k)+3=8*k+3 by omega]

#print axioms eTripleZero_front
#print axioms eTripleZero_run
#print axioms full_E_triple_zero
end BB6.Agent32ETriple
