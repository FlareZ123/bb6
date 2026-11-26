import Canonical59FiveParentMembership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Raw124Canonical64Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

/-- Raw124 is the E1=1LF sibling of the eight E1 parents already removed
from the Canonical76 roster. This is the exact table used by
BB6.Agent32Raw124ParentJoin.parent124. -/
abbrev p124 : PartialMachine :=
  refine BB6.Agent31Canonical59Membership.e1Base (4,true) (some ⟨true,false,5⟩)

theorem p124_root :
    p124 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Exact unique membership in the source-accepted Canonical64 roster. -/
theorem p124_member_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p124)).length = 1 := by
  decide

/-- Raw124 survives the five-parent Canonical64 batch and remains a unique
member of its exact 59-entry complement. -/
theorem p124_member_count59 :
    (BB6.Agent31Canonical59Membership.roster59.filter
      (fun e => sameTable e.2 p124)).length = 1 := by
  decide

theorem p124_distinct_from_five :
    ∀ p ∈ BB6.Agent31Canonical59Membership.parents,
      sameTable p p124 = false := by
  intro p hp
  simp only [BB6.Agent31Canonical59Membership.parents, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide

#eval BB6.Agent3Canonical64Raw120.roster64.findIdx
  (fun e => sameTable e.2 p124)
#eval BB6.Agent31Canonical59Membership.roster59.findIdx
  (fun e => sameTable e.2 p124)

#print axioms p124_root
#print axioms p124_member_count64
#print axioms p124_member_count59
#print axioms p124_distinct_from_five

end BB6.Agent4Raw124Canonical64Membership
