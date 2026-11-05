import Agent6Pump15
import BB429Rank
import Lean.Elab.Tactic.Omega

namespace Agent6PumpTail
set_option maxRecDepth 5000
set_option maxHeartbeats 10000000

/-- The small exceptional tail immediately after the 2297-cycle affine phase. -/
theorem tail_19 :
  BB429.run 19 (11,1223294)=some (0,1223392) := by decide

/-- A single proved source-map macro return certificate replacing 39068
explicit transition evaluations with a 2297-cycle rank-linear induction. -/
theorem run_39068 :
  BB429.run 39068 (11,1048722)=some (0,1223392) := by
  have hp := Agent6Pump15.run_cycles_2297 2297 (by decide)
  rw [show (39068:Nat)=17*2297+19 by decide, BB429.run_add,hp]
  exact tail_19

#print axioms tail_19
#print axioms run_39068
end Agent6PumpTail
