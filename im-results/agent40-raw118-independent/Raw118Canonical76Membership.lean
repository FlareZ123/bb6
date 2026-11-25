import Raw118CanonicalMembership
import CanonicalTwoParentGraft

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw118Canonical76

open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalRefinement
open BB6.Agent47CanonicalTwoParent
open BB6.Agent16Raw118

/-- Raw118 is distinct from the raw107 parent removed by the first graft. -/
theorem parent_not_p107 : sameTable parent p107 = false := by
  decide

/-- Raw118 is distinct from the raw114 parent removed by the second graft. -/
theorem parent_not_p114 : sameTable parent p114 = false := by
  decide

/-- The exact Raw118 address survives the raw107 graft of canonical78. -/
theorem parent_mem_roster107 :
    (parentAddress, parent) ∈ roster107 := by
  unfold roster107
  unfold graftRoster
  apply List.mem_flatMap.mpr
  refine ⟨(parentAddress, parent), parent_mem_canonical78, ?_⟩
  simp [graftEntry, parent_not_p107]

/-- Raw118 is one of the 76 retained representatives after both raw107 and
raw114 grafts, so its local parent bound can be consumed as one hLeaves goal. -/
theorem parent_mem_roster76 :
    (parentAddress, parent) ∈ roster76 := by
  unfold roster76
  unfold graftRoster
  apply List.mem_flatMap.mpr
  refine ⟨(parentAddress, parent), parent_mem_roster107, ?_⟩
  simp [graftEntry, parent_not_p114]

#print axioms parent_not_p107
#print axioms parent_not_p114
#print axioms parent_mem_roster76

end BB6.Agent40Raw118Canonical76
