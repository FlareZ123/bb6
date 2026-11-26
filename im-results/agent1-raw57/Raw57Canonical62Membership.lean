import Canonical62Raw112Raw58Integrated
import Raw57ParentBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw57Canonical62Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier
open BB6.Agent4Canonical62Raw112Raw58

/-- The exact Raw57 six-hole parent E1=0LA. -/
abbrev p57 : PartialMachine := BB6.Agent1Raw57Parent.parent

theorem p57_root :
    p57 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Raw57 should survive the independently integrated Raw112+Raw58 cuts.
    This is only an exact membership certificate, not a third-parent cut. -/
theorem p57_parent_count62 :
    (roster62.filter (fun e => sameTable e.2 p57)).length = 1 := by
  decide

/-- Expected zero-based position after removing Raw112 and Raw58. -/
theorem p57_index62 :
    roster62.findIdx (fun e => sameTable e.2 p57) = 33 := by
  decide

#print axioms p57_root
#print axioms p57_parent_count62
#print axioms p57_index62

end BB6.Agent1Raw57Canonical62Membership
