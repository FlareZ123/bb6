import Raw56RootCut
import Raw56E1REAll

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw56Root
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- The generated child table and the hand-written E1=0RE refinement are
    extensionally identical; use the checked finite table comparison rather
    than relying on a brittle simplifier unfolding path. -/
theorem child_table_eq : BB6.Agent1Raw56.Raw56E1RE.p = e1RE := by
  exact sameTable_sound (by decide)

/-- Compose the source-checked E1=0RE child with the exact first-query
    Raw56 frontier, retaining all other canonical representatives. -/
theorem sound19_closed :
    ∀ m, TNFQuotientCompatible parent m →
      WeightedBound 7014 m ∨ ∃ e ∈ remaining19, TNFQuotientCompatible e.2 m := by
  apply sound19
  intro m hm
  exact BB6.Agent1Raw56.Raw56E1RE.all_quotient m (child_table_eq.symm ▸ hm)

#print axioms child_table_eq
#print axioms sound19_closed
end BB6.Agent1Raw56Root
