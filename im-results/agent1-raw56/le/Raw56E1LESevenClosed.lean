import Raw56E1LESevenCut
import Raw56E1LEFiveClosed
import Raw56LE0RAPartialAll
import Raw56LE0LFPartialAll

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- Authentic E0=0RA and 0LF tables agree exactly with the canonical source
    children in the literal E1=0LE root. -/
theorem eqRAPartial :
    BB6.Agent1Raw56.LE0RAPartial.p = raPartial :=
  sameTable_sound (by decide)

theorem eqLFPartial :
    BB6.Agent1Raw56.LE0LFPartial.p = lfPartial :=
  sameTable_sound (by decide)

/-- All seven remaining first-query siblings and the exact fifteen plus one
    second-level residuals remain explicit. This theorem is NOT an
    unconditional bound or an entire E1=0LE Cover. -/
theorem sound7_closed :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 40000 m ∨
      (∃ e ∈ remaining7, TNFQuotientCompatible e.2 m) ∨
      (∃ e ∈ BB6.Agent1Raw56.LE0RAPartial.remaining15,
        TNFQuotientCompatible e.2 m) ∨
      (∃ e ∈ BB6.Agent1Raw56.LE0LFPartial.remaining1,
        TNFQuotientCompatible e.2 m) :=
  sound7
    (fun m hm => BB6.Agent1Raw56.LE0RB.all_quotient m (eqRB5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE0RC.all_quotient m (eqRC5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE0LB.all_quotient m (eqLB5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE1LA.all_quotient m (eqLA5.symm ▸ hm))
    (fun m hm => BB6.Agent1Raw56.LE1RA.all_quotient m (eqRA5.symm ▸ hm))
    BB6.Agent1Raw56.LE0RAPartial.remaining15
    BB6.Agent1Raw56.LE0LFPartial.remaining1
    (fun m hm =>
      BB6.Agent1Raw56.LE0RAPartial.sound15 m (eqRAPartial.symm ▸ hm))
    (fun m hm =>
      BB6.Agent1Raw56.LE0LFPartial.sound1 m (eqLFPartial.symm ▸ hm))

#print axioms sound7_closed
end BB6.Agent1Raw56E1LE
