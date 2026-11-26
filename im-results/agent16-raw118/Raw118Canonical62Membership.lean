import Canonical62Raw112Raw58Integrated
import Raw118Base
import Raw118CanonicalCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw118Canonical62Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31StableParentBatch
open BB6.Agent4Canonical62Raw112Raw58

/-- The exact Raw118 parent, with the same definition used by the conditional cut. -/
abbrev p118 : PartialMachine := BB6.Agent16Raw118CanonicalCut.p118

theorem p118_eq_raw118_parent :
    p118 = BB6.Agent16Raw118.parent := by
  rfl

theorem p118_root :
    p118 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent16Raw118CanonicalCut.parent_root

/-- Raw118 survives the joint Raw112+Raw58 cut exactly once in Agent4's
    Canonical62 draft. This is a membership certificate only: it defines no
    roster and makes no claim that the Raw118 parent Cover has passed. -/
theorem p118_parent_count62 :
    (roster62.filter (fun e => sameTable e.2 p118)).length = 1 := by
  decide

#print axioms p118_eq_raw118_parent
#print axioms p118_root
#print axioms p118_parent_count62

end BB6.Agent16Raw118Canonical62Membership
