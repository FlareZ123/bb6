import Canonical64Raw120Integrated
import Raw118Base
import Raw118CanonicalCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw118Canonical64Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch BB6.Agent31Canonical65AfterThree

abbrev p118 : PartialMachine := BB6.Agent16Raw118CanonicalCut.p118

/-- The conditional-cut parent is definitionally the exact Raw118 parent
    covered by Raw118Complete.parent_cover. -/
theorem p118_eq_raw118_parent :
    p118 = BB6.Agent16Raw118.parent := by
  rfl

theorem p118_root :
    p118 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent16Raw118CanonicalCut.parent_root

/-- Exact, unique sameTable membership in the accepted Canonical64 roster.
    This is only a membership certificate: it defines no competing roster
    and makes no claim that the Raw118 parent Cover has passed. -/
theorem p118_parent_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p118)).length = 1 := by
  decide

#print axioms p118_eq_raw118_parent
#print axioms p118_root
#print axioms p118_parent_count64

end BB6.Agent16Raw118Canonical64Membership
