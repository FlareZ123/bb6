import ExceptionalESafeCanonical
import E3SourceRejoin
import DRegularSourceShift

set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

namespace BB6.Agent37ExceptionalEReentryClassification

open CryptidBoundary BB6.BoundaryPadding

/-- A source-canonical closure for every E exit except the q≡1 (mod 3),
    q≥4 P2-reset family: q=1 is covered by Agent 25's verified all-residue
    q1b1 theorem, while q≥2 and q≠1 mod 3 are covered by the uniform
    safe-packet theorem developed here. -/
theorem all_E_reentry_canonical_except_q1_mod3
    (k q : Nat)
    (h : q=1 ∨ (2 ≤ q ∧ q % 3 ≠ 1)) :
    ∃ T a q' b,
      ObsEq
        (run T (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (DRegularSource.sourceSection ⟨a,q',b⟩) ∧
      DRegular.Canon ⟨a,q',b⟩ := by
  rcases h with hq1 | hsafe
  · subst q
    obtain ⟨T,s,hcanon,hobs⟩ :=
      BB6.Agent25E3SourceBridge.q1b1_rejoins_regular k
    refine ⟨T,s.a,s.q,s.b,?_,hcanon⟩
    simpa [BB6.Agent25E3SourceBridge.sourceStartK] using hobs
  · obtain ⟨T,a,q',b,hobs,hcanon⟩ :=
      BB6.Agent37ExceptionalESafeCanonical.all_E_safe_reentry_canonical
        k q hsafe.1 hsafe.2
    exact ⟨BB6.Agent32EAll.duration k (q-1) + T,a,q',b,hobs,hcanon⟩

#print axioms all_E_reentry_canonical_except_q1_mod3

end BB6.Agent37ExceptionalEReentryClassification
