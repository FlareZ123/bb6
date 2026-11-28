import Raw56E1LEThreeCut
import Raw56LE0RBAll
import Raw56LE0RCAll
import Raw56LE0LBAll
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

theorem eqRB3 : BB6.Agent1Raw56.LE0RB.p = rb := sameTable_sound (by decide)
theorem eqRC3 : BB6.Agent1Raw56.LE0RC.p = rc := sameTable_sound (by decide)
theorem eqLB3 : BB6.Agent1Raw56.LE0LB.p = lb := sameTable_sound (by decide)

theorem sound11_closed : ∀ m, TNFQuotientCompatible p m →
    WeightedBound 7014 m ∨ ∃ e ∈ remaining11, TNFQuotientCompatible e.2 m :=
  sound11
    (fun m hm => BB6.Agent1Raw56.LE0RB.all_quotient m (eqRB3.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE0RC.all_quotient m (eqRC3.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE0LB.all_quotient m (eqLB3.symm ▸ hm))

#print axioms sound11_closed
end BB6.Agent1Raw56E1LE
