import Canonical64Raw120Integrated
import Raw122CompleteParent

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent43Raw122Canonical

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalRefinement
open BB6.Agent47CanonicalFrontier
open BB6.Agent3Canonical64Raw120
open BB6.Agent43Raw122

/-- The Raw122 six-hole parent is a first-one normalized parent. -/
abbrev p122 : PartialMachine := BB6.Agent43Raw122.parent

theorem p122_root :
    p122 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Exact Cover interface consumed by the Canonical64/63 integration. -/
theorem parent_cover : Cover (WeightedBound 6766859) p122 := by
  intro m hm
  exact BB6.Agent43Raw122CompleteParent.parent_bound m hm

#print axioms p122_root
#print axioms parent_cover

end BB6.Agent43Raw122Canonical
