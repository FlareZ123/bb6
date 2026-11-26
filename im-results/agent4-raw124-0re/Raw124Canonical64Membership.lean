import Canonical64Raw120Integrated

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Raw124Canonical64Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31StableParentBatch

/-- Raw124 is the E1=1LF sibling of the eight E1 parents already removed
from the Canonical76 roster. This is the exact table used by
BB6.Agent32Raw124ParentJoin.parent124. -/
abbrev p124 : PartialMachine :=
  refine e1Base (4,true) (some ⟨true,false,5⟩)

theorem p124_root :
    p124 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Exact unique membership in the source-accepted 64-entry roster.
This is only a membership preflight: it does not claim a Raw124 Cover,
remove any roster entry, or establish a smaller global frontier. -/
theorem p124_member_count :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p124)).length = 1 := by
  decide

#eval BB6.Agent3Canonical64Raw120.roster64.findIdx
  (fun e => sameTable e.2 p124)

#print axioms p124_root
#print axioms p124_member_count

end BB6.Agent4Raw124Canonical64Membership
