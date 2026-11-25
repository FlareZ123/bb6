import Root109Membership
import CanonicalTwoParentGraft

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13Canonical77HeldMembership

open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalRefinement
open BB6.Agent47Canonical78
open BB6.Agent47CanonicalTwoParent
open BB6.Agent13CrossRouteHeldLeaf109

/-- The raw10 B0=1LC parent is already a canonical first-one residual,
    before the raw114 parent is grafted. -/
theorem parent_in_canonical78 :
    ∃ e ∈ BB6.Agent47Canonical78.roster,
      BB6.Agent31FourHoleRoster.sameTable e.2 firstOneB0_1LC = true := by
  decide

/-- The raw114 parent is a different first-one cylinder. -/
theorem parent_disjoint_from_raw114_parent :
    BB6.Agent31FourHoleRoster.sameTable firstOneB0_1LC
      BB6.Agent47CanonicalTwoParent.p114 = false := by
  decide

/-- The post-raw114 77 roster is exactly the raw114 graft of the accepted
    78 roster with an empty replacement, as in CanonicalRaw114Accepted.lean.
    This local definition avoids importing the large raw114 proof artifact. -/
noncomputable def canonical77Roster : List (List BB6Coverage.Move × BB6Coverage.PartialMachine) :=
  BB6.Agent47CanonicalRefinement.graftRoster
    BB6.Agent47CanonicalTwoParent.p114 [] BB6.Agent47Canonical78.roster

/-- The B0=1LC parent survives the raw114 graft as an exact member of the
    current 77-way roster; it is not merely an unrelated pre-graft branch. -/
theorem parent_in_canonical77 :
    ∃ e ∈ canonical77Roster,
      BB6.Agent31FourHoleRoster.sameTable e.2 firstOneB0_1LC = true := by
  decide

#print axioms parent_in_canonical78
#print axioms parent_disjoint_from_raw114_parent
#print axioms parent_in_canonical77

end BB6.Agent13Canonical77HeldMembership
