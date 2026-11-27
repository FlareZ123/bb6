import Lean.Elab.Tactic.Omega
import DRegularSourceShift
import ExceptionalESafeCanonical

set_option maxRecDepth 8192
set_option maxHeartbeats 15000000

namespace BB6.Agent37RegularSafeEBridge

open CryptidBoundary BB6.BoundaryPadding

/-- Any exact source-certified regular prefix ending at an exceptional
    E-sector L(3k+4,q,1) with q>=2 and q%3!=1 can be extended beyond the
    E-event to a later canonical source section. Quantification over the
    entire model prefix length n makes this reusable for genuine blank
    starts, not only prepared packets. -/
theorem regular_prefix_then_safe_E
    (s t : DRegular.L) (n k q : Nat)
    (hcanon : DRegular.Canon s)
    (hmodel : DRegular.run n s = some t)
    (hshape : t = (⟨3*k+4,q,1⟩ : DRegular.L))
    (hq : 2 ≤ q) (hqmod : q % 3 ≠ 1) :
    ∃ T a q' b,
      ObsEq
        (CryptidBoundary.run (DRegular.accumulated n s + T)
          (DRegularSource.sourceSection s))
        (DRegularSource.sourceSection ⟨a,q',b⟩) ∧
      DRegular.Canon ⟨a,q',b⟩ := by
  obtain ⟨u,a,q',b,hE,houtCanon⟩ :=
    BB6.Agent37ExceptionalESafeCanonical.all_E_safe_reentry_canonical
      k q hq hqmod
  have hreg : ObsEq
      (CryptidBoundary.run (DRegular.accumulated n s)
        (DRegularSource.sourceSection s))
      (DRegularSource.sourceSection t) :=
    (BB6.DRegularSourceShift.paired_original_run
      s t n 0 hcanon hmodel).1
  have hE' : ObsEq
      (CryptidBoundary.run (BB6.Agent32EAll.duration k (q-1) + u)
        (DRegularSource.sourceSection t))
      (DRegularSource.sourceSection ⟨a,q',b⟩) := by
    simpa [hshape] using hE
  have h := BB6.BoundaryPadding.source_chain
    (DRegular.accumulated n s)
    (BB6.Agent32EAll.duration k (q-1) + u)
    (DRegularSource.sourceSection s)
    (DRegularSource.sourceSection t)
    (DRegularSource.sourceSection ⟨a,q',b⟩)
    hreg hE'
  exact ⟨BB6.Agent32EAll.duration k (q-1) + u,
    a,q',b,h,houtCanon⟩

#print axioms regular_prefix_then_safe_E

end BB6.Agent37RegularSafeEBridge
