import AllQ1101101100
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 4096

namespace BB6.Agent2AllQE1101101100
open CryptidBoundary

/- Source-connected conditional E halting cylinder, with an unbounded
  (10)^q variable-length scanner prefix and arbitrary trailing right bits.
  The conclusion concerns the ORIGINAL six-state machine frozen halt state,
  not an arbitrary prepared E boundary. -/
theorem full_E_all_q_halt (k q : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+106+2*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairR q ++ word ++ ys)))).st = 6 := by
  have ht : 12*k*k+41*k+106+2*q =
    (12*k*k+41*k+33)+(73+2*q) := by omega
  rw [ht,run_add,prefix_E]
  have hp : pairs (4*k+3) =
      true :: false :: pairs (4*k+2) := by
    rw [show 4*k+3 = (4*k+2)+1 by omega]
    rfl
  rw [hp]
  change (run (73+2*q)
    (⟨[false,false,true] ++
      (false :: pairs (4*k+2) ++ [true,true]),
      false,pairR q ++ word ++ ys,4⟩ : Cfg)).st = 6
  exact all_q_e_terminal_halt q _ ys

#print axioms full_E_all_q_halt
end BB6.Agent2AllQE1101101100
