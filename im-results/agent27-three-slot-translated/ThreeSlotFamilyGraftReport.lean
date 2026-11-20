import ThreeSlotFamilyGraft

/-!
Exact report target for the combined five-slot plus 80-member three-slot audit.

This theorem is deliberately kept separate from the core family graft so that
the translated-family proof closure can be checked independently of the
potentially expensive report reduction. It must be compiled with the same
Lean 4.36.0-rc2 source closure before its numerical conclusion is treated as
accepted.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace BB6Coverage.ThreeSlotFamilies

/-- Expected combined report: the five-slot report plus the 80 disjoint
    three-slot cylinders, each of mass 25^9. This is a proof target, not an
    accepted result until Lean checks the theorem and its axiom profile. -/
theorem familyPlusFiveAudit_report_exact :
    familyPlusFiveAudit.report =
      (40876013183593750, 18728631591796875) := by
  decide

#print axioms familyPlusFiveAudit_report_exact

end BB6Coverage.ThreeSlotFamilies
