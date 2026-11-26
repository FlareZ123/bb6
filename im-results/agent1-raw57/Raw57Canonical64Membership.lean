import Canonical64Raw120Integrated
import Raw57ParentBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw57Canonical64Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier
open BB6.Agent3Canonical64Raw120

/-- The exact six-hole Raw57 parent (E1=0LA) from canonical-124 residual 57. -/
abbrev p57 : PartialMachine := BB6.Agent1Raw57Parent.parent

theorem p57_root :
    p57 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Exact, unique sameTable membership in the accepted Canonical64 roster.
    This is only a membership certificate: it defines no competing roster
    and makes no global soundness claim. -/
theorem p57_parent_count64 :
    (roster64.filter (fun e => sameTable e.2 p57)).length = 1 := by
  decide

/-- The Raw57 parent is expected at zero-based position 33 in roster64. -/
theorem p57_index64 :
    roster64.findIdx (fun e => sameTable e.2 p57) = 33 := by
  decide

#print axioms p57_root
#print axioms p57_parent_count64
#print axioms p57_index64

end BB6.Agent1Raw57Canonical64Membership
