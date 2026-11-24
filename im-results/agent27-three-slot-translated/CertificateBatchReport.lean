import CertificateBatch
import IncrementalAuditReport

namespace BB6Coverage

/-- Every later source is disjoint from every earlier one. Repeated sources
    do not satisfy this condition, even when their proof terms differ. -/
def PairwiseCertificateDisjoint {good : Machine → Prop}
    (certs : List (LeafCertificate good)) : Prop :=
  certs.Pairwise (fun c d => ∀ m, compatible d.1 m → ¬ compatible c.1 m)

/-- Exact batch-report update, using only the old report, the sum of the
    individual cylinder masses, initial openness, and pairwise disjointness.
    In particular, no intermediate or final giant tree report is evaluated. -/
theorem addCertificates_report_of_open {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) (certs : List (LeafCertificate good))
    (hsub : ∀ c ∈ certs, ∀ m, compatible c.1 m → compatible p m)
    (hfresh : ∀ c ∈ certs, ∀ m, compatible c.1 m → audit.open m)
    (hdis : PairwiseCertificateDisjoint certs) :
    (addCertificates audit certs).report =
      (audit.report.1 + (certs.map (fun c => cylinderMass c.1)).sum,
       audit.report.2 - (certs.map (fun c => cylinderMass c.1)).sum) := by
  induction certs generalizing audit with
  | nil => simp [addCertificates]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hpair := List.pairwise_cons.mp hdis
      have htailSub : ∀ d ∈ cs, ∀ m, compatible d.1 m → compatible p m :=
        fun d hd => hsub d (by simp [hd])
      have htailFresh : ∀ d ∈ cs, ∀ m, compatible d.1 m →
          (addCertificate audit c.1 c.2).open m := by
        intro d hd m hm
        apply (addCertificate_open_iff audit c.1 c.2 m (htailSub d hd m hm)).mpr
        exact ⟨hfresh d (by simp [hd]) m hm, hpair.1 d hd m hm⟩
      change (addCertificates (addCertificate audit c.1 c.2) cs).report = _
      rw [ih _ htailSub htailFresh hpair.2]
      rw [addCertificate_report_of_open audit c.1 c.2 (hsub c hc) (hfresh c hc)]
      simp [Nat.add_assoc, Nat.sub_sub]

/-- Global-root version with automatic root containment. -/
theorem addCertificates_global_report_of_open {good : Machine → Prop}
    (audit : FrontierAudit good emptyTable) (certs : List (LeafCertificate good))
    (hfresh : ∀ c ∈ certs, ∀ m, compatible c.1 m → audit.open m)
    (hdis : PairwiseCertificateDisjoint certs) :
    (addCertificates audit certs).report =
      (audit.report.1 + (certs.map (fun c => cylinderMass c.1)).sum,
       audit.report.2 - (certs.map (fun c => cylinderMass c.1)).sum) :=
  addCertificates_report_of_open audit certs (fun _ _ m _ => empty_compatible m) hfresh hdis

#print axioms addCertificates_report_of_open
#print axioms addCertificates_global_report_of_open

end BB6Coverage
