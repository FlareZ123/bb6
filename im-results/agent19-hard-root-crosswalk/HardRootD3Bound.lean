import Lean.Elab.Tactic.Omega
import HardRootLeaves

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19HardRoot
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath

/-- Step 23 is the first query of the ordinary D1 transition, not a halt. -/
theorem D3_query23 : (run D3 23 blank).map readSlot = some (3,true) := by decide

theorem D3_live24 : (run D3 24 blank).isSome = true := by decide

theorem D3_noHaltUpTo23 (k : Nat) (hk : k ≤ 23) : ¬ HaltsAfter D3 k := by
  intro hh
  have h24 : run D3 24 blank = none := by
    have hsum : k + 1 + (24 - (k+1)) = 24 := by omega
    rw [← hsum]
    exact run_none_add D3 blank (k+1) (24-(k+1)) hh.2
  have hlive := D3_live24
  simp [h24] at hlive

#print axioms D3_query23
#print axioms D3_live24
#print axioms D3_noHaltUpTo23

end BB6.Agent19HardRoot
