import Canonical58SixParentMembership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw124Canonical58Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch

/-- The exact Raw124 E1=1LF parent, independently expressed from its
    branch proof so roster membership is checked before importing that proof. -/
abbrev e1Base : PartialMachine := (pathEnd root 2 (path.take 4)).1

abbrev p124 : PartialMachine :=
  refine e1Base (4,true) (some ⟨true,false,5⟩)

/-- Raw124 occurs exactly once in the accepted Canonical64 source roster. -/
theorem p124_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p124)).length = 1 := by decide

/-- Raw124 is distinct from all six parents in the prepared Canonical58 cut. -/
theorem p124_distinct_from_six :
    ∀ p ∈ BB6.Agent31Canonical58Membership.parents,
      sameTable p p124 = false := by decide

/-- Consequently the Raw124 table remains exactly once in the 58-entry
    residual list after the six-parent Canonical58 filter. -/
theorem p124_count58 :
    (BB6.Agent31Canonical58Membership.roster58.filter
      (fun e => sameTable e.2 p124)).length = 1 := by decide

/-- Removing Raw124 from that exact 58-entry list leaves 57 representatives. -/
noncomputable def roster57 : List (Nat × PartialMachine) :=
  removeParents [p124] BB6.Agent31Canonical58Membership.roster58

theorem count57 : roster57.length = 57 := by decide

theorem p124_root :
    p124 initialSlot = some (some ⟨true,true,1⟩) := by decide

#print axioms p124_count64
#print axioms p124_distinct_from_six
#print axioms p124_count58
#print axioms count57
#print axioms p124_root

end BB6.Agent2Raw124Canonical58Membership
