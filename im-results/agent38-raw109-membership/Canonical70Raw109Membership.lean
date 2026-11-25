import Canonical70Raw121Raw110RosterOnly
import Raw109Cut
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent38Raw109Membership

open BB6.Agent47CanonicalRefinement

/-- The Raw109 parent is a retained representative after the six canonical72
    cuts and the additional Raw121 and raw110 cuts. This exact membership
    check is the prerequisite for a further roster graft. -/
theorem parent_present :
    ∃ e ∈ BB6.Agent8Canonical70Raw121Raw110RosterOnly.roster,
      sameTable e.2 BB6.Agent4Raw109Cut.parent = true := by
  decide

/-- Filter the Raw109 parent cylinder from the canonical70 list. -/
noncomputable def roster :=
  graftRoster BB6.Agent4Raw109Cut.parent []
    BB6.Agent8Canonical70Raw121Raw110RosterOnly.roster

/-- Expected count after the additional Raw109 cut. -/
theorem count : roster.length = 69 := by
  decide

#print axioms parent_present
#print axioms count

end BB6.Agent38Raw109Membership
