import Raw56E1LEFiveCut
import Raw56LE0RBAll
import Raw56LE0RCAll
import Raw56LE0LBAll
import Raw56LE1LAAll
import Raw56LE1RAAll
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

theorem eqRB5 : BB6.Agent1Raw56.LE0RB.p = rb := sameTable_sound (by decide)
theorem eqRC5 : BB6.Agent1Raw56.LE0RC.p = rc := sameTable_sound (by decide)
theorem eqLB5 : BB6.Agent1Raw56.LE0LB.p = lb := sameTable_sound (by decide)
theorem eqLA5 : BB6.Agent1Raw56.LE1LA.p = la := sameTable_sound (by decide)
theorem eqRA5 : BB6.Agent1Raw56.LE1RA.p = ra := sameTable_sound (by decide)

/-- Five complete literal sibling covers, of which 1RA has threshold 14000. -/
theorem sound9_closed : ∀ m, TNFQuotientCompatible p m →
    WeightedBound 14000 m ∨ ∃ e ∈ remaining9, TNFQuotientCompatible e.2 m :=
  sound9
    (fun m hm => BB6.Agent1Raw56.LE0RB.all_quotient m (eqRB5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE0RC.all_quotient m (eqRC5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE0LB.all_quotient m (eqLB5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE1LA.all_quotient m (eqLA5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE1RA.all_quotient m (eqRA5.symm ▸ hm))

#print axioms sound9_closed
end BB6.Agent1Raw56E1LE
