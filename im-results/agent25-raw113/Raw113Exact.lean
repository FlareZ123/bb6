import Raw113ParentExact
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent25Raw113
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6Coverage.Agent10ZipAudit BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- Consume the concrete parent certificate in any current quotient roster,
    including future versions. All other parents are preserved by graftRoster. -/
theorem graft113_sound {B : Nat} {roster : List Entry}
    (hB : 2674 ≤ B)
    (hroot : ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ roster, TNFQuotientCompatible e.2 m) :
    ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ graftRoster p113 [] roster, TNFQuotientCompatible e.2 m :=
  graftRoster_sound p113_root hroot
    (fun m hm => Or.inl ((exact113 B).mpr hB m hm))

#print axioms attained113
#print axioms exact113
#print axioms graft113_sound
end BB6.Agent25Raw113
