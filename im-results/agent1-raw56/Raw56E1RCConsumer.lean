import Raw56E1RCCut
import Raw56RCRDAll
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

theorem rd_table_eq : BB6.Agent1Raw56.RCRD.p = rd := sameTable_sound (by decide)
theorem sound18_closed : ∀ m, TNFQuotientCompatible p m →
    WeightedBound 7014 m ∨ ∃ e ∈ remaining18, TNFQuotientCompatible e.2 m := by
  apply sound18
  intro m hm
  exact BB6.Agent1Raw56.RCRD.all_quotient m (rd_table_eq.symm ▸ hm)
#print axioms rd_table_eq
#print axioms sound18_closed
end BB6.Agent1Raw56E1RC
