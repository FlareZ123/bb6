import Canonical59FiveParentMembership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent29Raw83Canonical59Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical59Membership

/-- Raw83's exact six-hole table:
    1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RA.
    It is the E1=0LB cylinder with B1=1LF and F1=0RA fixed. -/
abbrev p83 : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨false,true,0⟩)

/-- Raw83 retains the canonical first-one root transition. -/
theorem p83_root :
    p83 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Exact table membership in the original 64-entry Canonical64 roster. -/
theorem p83_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p83)).length = 1 := by
  decide

/-- Raw83 is still present exactly once after the five already-proposed
    parents p58, p59, p108, p115 and p119 are removed. -/
theorem p83_count59 :
    (roster59.filter (fun e => sameTable e.2 p83)).length = 1 := by
  decide

/-- The new parent is distinct from every one of the five existing cuts. -/
theorem p83_distinct_from_five :
    ∀ p ∈ parents, sameTable p p83 = false := by
  decide

#print axioms p83_root
#print axioms p83_count64
#print axioms p83_count59
#print axioms p83_distinct_from_five

end BB6.Agent29Raw83Canonical59Membership
