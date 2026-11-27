import Raw56E1LECut
import Raw56LE0RBAll
import Raw56LE0RCAll
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

theorem eqRB : BB6.Agent1Raw56.LE0RB.p = rb := sameTable_sound (by decide)
theorem eqRC : BB6.Agent1Raw56.LE0RC.p = rc := sameTable_sound (by decide)

theorem sound12_closed : ∀ m, TNFQuotientCompatible p m →
    WeightedBound 7014 m ∨ ∃ e ∈ remaining12, TNFQuotientCompatible e.2 m :=
  sound12
    (fun m hm => BB6.Agent1Raw56.LE0RB.all_quotient m (eqRB.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE0RC.all_quotient m (eqRC.symm ▸ hm))

#print axioms sound12_closed
end BB6.Agent1Raw56E1LE
