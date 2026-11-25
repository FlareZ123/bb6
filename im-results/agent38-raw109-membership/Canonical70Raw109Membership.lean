import Canonical71Raw121RosterOnly
import Raw109Cut
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent38Raw109Membership

open BB6.Agent47CanonicalRefinement

/-- The Raw109 parent is a retained representative after the six canonical72
    cuts and the additional Raw121 cut. This exact membership check is the
    prerequisite for using its parent certificate as another roster graft. -/
theorem parent_present :
    ∃ e ∈ BB6.Agent8Canonical71Raw121RosterOnly.roster,
      sameTable e.2 BB6.Agent4Raw109Cut.parent = true := by
  decide

/-- Filter the Raw109 parent cylinder from the canonical71 list. -/
noncomputable def roster :=
  graftRoster BB6.Agent4Raw109Cut.parent []
    BB6.Agent8Canonical71Raw121RosterOnly.roster

/-- Expected count after the additional Raw109 cut. -/
theorem count : roster.length = 70 := by
  decide

#print axioms parent_present
#print axioms count

end BB6.Agent38Raw109Membership
