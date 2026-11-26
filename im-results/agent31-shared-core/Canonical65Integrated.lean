import Canonical68Integrated
import Canonical65AfterThree

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical65Integrated
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier
open BB6.Agent31Canonical65AfterThree

/-- No parent certificate is assumed: all eleven parent closures are imported
and consumed. Only these 65 residual quotient representatives remain. -/
theorem sound65_integrated :
    ∀ m, compatible root m → WeightedBound 6766859 m ∨
      ∃ e ∈ roster65, TNFQuotientCompatible e.2 m :=
  sound65 (by decide) BB6.Agent31Canonical68Integrated.sound68_integrated

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster65, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound65_integrated hLeaves champ

#print axioms sound65_integrated
#print axioms exact_at_target

end BB6.Agent31Canonical65Integrated
