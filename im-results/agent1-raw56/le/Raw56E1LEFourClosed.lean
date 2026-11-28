import Raw56E1LEFourCut
import Raw56LE0RBAll
import Raw56LE0RCAll
import Raw56LE0LBAll
import Raw56LE1LAAll
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

theorem eqRB4 : BB6.Agent1Raw56.LE0RB.p = rb := sameTable_sound (by decide)
theorem eqRC4 : BB6.Agent1Raw56.LE0RC.p = rc := sameTable_sound (by decide)
theorem eqLB4 : BB6.Agent1Raw56.LE0LB.p = lb := sameTable_sound (by decide)
theorem eqLA4 : BB6.Agent1Raw56.LE1LA.p = la := sameTable_sound (by decide)

/-- Only after all four exact source Covers are imported, close the residual 14→10 cut. -/
theorem sound10_closed : ∀ m, TNFQuotientCompatible p m →
    WeightedBound 7014 m ∨ ∃ e ∈ remaining10, TNFQuotientCompatible e.2 m :=
  sound10
    (fun m hm => BB6.Agent1Raw56.LE0RB.all_quotient m (eqRB4.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE0RC.all_quotient m (eqRC4.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE0LB.all_quotient m (eqLB4.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE1LA.all_quotient m (eqLA4.symm ▸ hm))

#print axioms sound10_closed
end BB6.Agent1Raw56E1LE
