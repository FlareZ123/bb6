import Canonical58SixParentMembership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent29Raw83Canonical58Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical58Membership

/-- Raw83's exact four-hole parent, matching the generator's source expression:
    1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RA. -/
abbrev p83 : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨false,true,0⟩)

/-- The exact Raw83 parent retains the canonical first-one root transition. -/
theorem p83_root :
    p83 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Raw83 occurs exactly once in the residual roster after all six existing
    cuts p58, p59, p108, p113, p115 and p119. -/
theorem p83_count58 :
    (roster58.filter (fun e => sameTable e.2 p83)).length = 1 := by
  decide

/-- Raw83 is pairwise distinct from every one of the six existing parents. -/
theorem p83_distinct_from_six :
    ∀ p ∈ BB6.Agent31Canonical58Membership.parents, sameTable p p83 = false := by
  decide

/-- Explicit exact-table version using the same equality predicate as
    removeParents; this rules out a wildcard/compatibility interpretation. -/
theorem p83_exact_count58 :
    (BB6.Agent31Canonical58Membership.roster58.filter
      (fun e => BB6.Agent31FourHoleRoster.sameTable e.2 p83)).length = 1 := by
  decide

theorem p83_exact_distinct_from_six :
    ∀ p ∈ BB6.Agent31Canonical58Membership.parents,
      BB6.Agent31FourHoleRoster.sameTable p p83 = false := by
  decide

#print axioms p83_root
#print axioms p83_count58
#print axioms p83_distinct_from_six
#print axioms p83_exact_count58
#print axioms p83_exact_distinct_from_six

end BB6.Agent29Raw83Canonical58Membership
