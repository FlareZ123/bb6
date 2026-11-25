import Canonical70Raw121Raw110RosterOnly
import Raw112Base
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent38Raw112Membership

open BB6.Agent47CanonicalRefinement

/-- The raw112 parent remains represented after canonical72, raw121, and
    raw110 cuts. The canonical75→canonical74 proof already shows that one
    p112 representative survives raw117; this check verifies it also survives
    the additional cuts in the canonical70 route. -/
theorem parent_present :
    ∃ e ∈ BB6.Agent8Canonical70Raw121Raw110RosterOnly.roster,
      sameTable e.2 BB6.Agent47Raw112.parent = true := by
  decide

/-- Filter the raw112 parent from the canonical70 roster. -/
noncomputable def roster :=
  graftRoster BB6.Agent47Raw112.parent []
    BB6.Agent8Canonical70Raw121Raw110RosterOnly.roster

/-- Expected count after the additional raw112 cut. -/
theorem count : roster.length = 69 := by
  decide

#print axioms parent_present
#print axioms count

end BB6.Agent38Raw112Membership
