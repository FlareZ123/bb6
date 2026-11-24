import IncrementalAudit

namespace BB6Coverage

/-- A dependent source/certificate pair for one exact leaf graft. -/
abbrev LeafCertificate (good : Machine → Prop) :=
  { src : PartialMachine // Cover good src }

/-- Sequentially add a finite list of source certificates to the same
    frontier audit. The list is kept dependent so every certificate proves
    exactly the predicate for its own source partial table. -/
noncomputable def addCertificates {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) :
    List (LeafCertificate good) → FrontierAudit good p
  | [] => audit
  | c :: cs => addCertificates (addCertificate audit c.1 c.2) cs

/-- Exact open-set semantics for a batch of grafts: a machine remains open
    precisely when it was open before and is incompatible with every source
    cylinder in the batch. This is the finite-fold form of
    addCertificate_open_iff. -/
theorem addCertificates_open_iff {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) (certs : List (LeafCertificate good))
    (m : Machine) (hm : compatible p m) :
    (addCertificates audit certs).open m ↔
      audit.open m ∧ ∀ c ∈ certs, ¬ compatible c.1 m := by
  induction certs generalizing audit with
  | nil =>
      simp [addCertificates]
  | cons c cs ih =>
      change (addCertificates (addCertificate audit c.1 c.2) cs).open m ↔
        audit.open m ∧ ∀ d ∈ c :: cs, ¬ compatible d.1 m
      rw [ih (addCertificate audit c.1 c.2)]
      rw [addCertificate_open_iff audit c.1 c.2 m hm]
      simp [and_assoc]

/-- Every source-compatible machine is removed from the open set by a
    batch containing that source certificate. -/
theorem addCertificates_closes_member {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p)
    (certs : List (LeafCertificate good)) (c : LeafCertificate good)
    (hc : c ∈ certs) (m : Machine) (hm : compatible p m)
    (hopen : (addCertificates audit certs).open m) :
    ¬ compatible c.1 m := by
  exact ((addCertificates_open_iff audit certs m hm).mp hopen).2 c hc

#print axioms addCertificates_open_iff
#print axioms addCertificates_closes_member

end BB6Coverage
