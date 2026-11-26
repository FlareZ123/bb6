import CanonicalSelectedParentIntegrated
import Raw122Base

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw122Canonical59Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6.Agent32CanonicalSelectedIntegrated
open BB6.Agent43Raw122

/-- The exact Raw122 parent table used by the 24-child parent-cover project. -/
abbrev p122 : PartialMachine := BB6.Agent43Raw122.parent

theorem p122_source_eq : p122 = BB6.Agent43Raw122.parent := rfl

theorem p122_root :
    p122 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent43Raw122.parent_root

/-- Raw122 occurs exactly once in the currently accepted 59-residual roster. -/
theorem p122_count59 :
    (rosterSelected.filter (fun e => sameTable e.2 p122)).length = 1 := by
  decide

#eval rosterSelected.findIdx (fun e => sameTable e.2 p122)

#print axioms p122_source_eq
#print axioms p122_root
#print axioms p122_count59

end BB6.Agent40Raw122Canonical59Membership
