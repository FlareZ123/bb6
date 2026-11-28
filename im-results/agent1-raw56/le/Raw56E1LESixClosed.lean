import Raw56E1LESixCut
import Raw56E1LEFiveClosed
import Raw56LE0LFFull

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

theorem eqLFFull :
    BB6.Agent1Raw56.LE0LFPartial.p = lf :=
  sameTable_sound (by decide)

/-- Five previously accepted children plus the complete E0=0LF child give an
    exact eight-residual conditional frontier at weighted threshold 40000. -/
theorem sound8_closed :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 40000 m ∨ ∃ e ∈ remaining8, TNFQuotientCompatible e.2 m :=
  sound8
    (fun m hm => BB6.Agent1Raw56.LE0RB.all_quotient m (eqRB5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE0RC.all_quotient m (eqRC5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE0LB.all_quotient m (eqLB5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE1LA.all_quotient m (eqLA5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE1RA.all_quotient m (eqRA5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE0LFFull.all_quotient m (eqLFFull.symm ▸ hm))

#print axioms sound8_closed
end BB6.Agent1Raw56E1LE
