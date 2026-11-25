import Lean.Elab.Tactic.Omega
import HardRootLeaves

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19HardRoot
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt

/-- The hard-root D3 machine reaches its unique undefined transition after
    23 primitive steps, so its score is exactly 24. -/
theorem D3_haltsAfter23 : HaltsAfter D3 23 := by
  decide

/-- Determinism makes 23 the only possible first-halting index. -/
theorem D3_halt_bound24 :
    ∀ k, HaltsAfter D3 k → k + 1 ≤ 24 := by
  intro k hk
  have heq := halting_time_unique D3 k 23 hk D3_haltsAfter23
  omega

/-- Every completion of D3's erased halt row is covered at the exact
    primitive score bound 24. This is the 25² hard-root leaf used by raw13. -/
theorem D3_cover24 :
    Cover (WeightedBound 24) (forgetHaltRows D3) :=
  (D3_cover_iff 24).2 D3_halt_bound24

#print axioms D3_haltsAfter23
#print axioms D3_halt_bound24
#print axioms D3_cover24

end BB6.Agent19HardRoot
