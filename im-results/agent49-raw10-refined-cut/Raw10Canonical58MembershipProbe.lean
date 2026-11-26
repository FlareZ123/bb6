import CanonicalSelectedParentIntegrated
import Raw10RefinedCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49Raw10Canonical58MembershipProbe

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch BB6.Agent49BoxBridge

abbrev p10 : PartialMachine := BB6.Agent49BoxBridge.firstOneB0_1LC

/-- Exact E1 parent definition used by the accepted Canonical59→58 delta. -/
abbrev e1Base : PartialMachine := (pathEnd root 2 (path.take 4)).1
abbrev p113 : PartialMachine :=
  refine e1Base (4,true) (some ⟨true,true,2⟩)

/-- Membership-only copy of the accepted Canonical58 roster constructor.
    The p113 Cover and global soundness remain those of the accepted graft. -/
def roster58 :=
  removeParents [p113] BB6.Agent32CanonicalSelectedIntegrated.rosterSelected

theorem count59 :
    BB6.Agent32CanonicalSelectedIntegrated.rosterSelected.length = 59 := by
  decide

theorem p113_count59 :
    (BB6.Agent32CanonicalSelectedIntegrated.rosterSelected.filter
      (fun e => sameTable e.2 p113)).length = 1 := by
  decide

theorem count58 : roster58.length = 58 := by
  decide

theorem p10_count59 :
    (BB6.Agent32CanonicalSelectedIntegrated.rosterSelected.filter
      (fun e => sameTable e.2 p10)).length = 1 := by
  decide

theorem p10_not_removed : sameTable p10 p113 = false := by
  decide

theorem p10_count58 :
    (roster58.filter (fun e => sameTable e.2 p10)).length = 1 := by
  decide

theorem raw59_retained :
    (roster58.filter (fun e => sameTable e.2 p59)).length = 1 := by
  decide

#eval (roster58.filter (fun e => sameTable e.2 p10)).map Prod.fst
#eval p10 initialSlot

#print axioms count59
#print axioms p113_count59
#print axioms count58
#print axioms p10_count59
#print axioms p10_not_removed
#print axioms p10_count58
#print axioms raw59_retained

end BB6.Agent49Raw10Canonical58MembershipProbe
