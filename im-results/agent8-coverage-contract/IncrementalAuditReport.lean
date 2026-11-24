import IncrementalAudit
import AuditReportMeasure

namespace BB6Coverage

/-- The report of a single graft inside an unresolved leaf, when the source
    fixes every already-fixed parent slot. -/
theorem graftCertificate_report_of_extends {good : Machine → Prop}
    (p src : PartialMachine) (cert : Cover good src)
    (hExt : ∀ s t, p s = some t → src s = some t) :
    (graftCertificate p src cert).report =
      (cylinderMass src, cylinderMass p - cylinderMass src) := by
  have hsub : ∀ m, compatible src m → compatible p m := by
    intro m hm s t ht
    exact hm s t (hExt s t ht)
  have h := audit_report_delta_of_open_iff
    (.unresolved p : FrontierAudit good p) (graftCertificate p src cert) hsub
    (fun m _ => by simp [FrontierAudit.open])
    (fun m hm => by
      simpa only [FrontierAudit.open, true_and] using graftCertificate_open_iff p src cert m hm)
  simpa only [FrontierAudit.report, Nat.zero_add] using h

/-- Adding an entirely open subcylinder transfers its exact cardinality
    from the unresolved coordinate to the certified coordinate. -/
theorem addCertificate_report_of_open {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) (src : PartialMachine) (cert : Cover good src)
    (hsub : ∀ m, compatible src m → compatible p m)
    (hfresh : ∀ m, compatible src m → audit.open m) :
    (addCertificate audit src cert).report =
      (audit.report.1 + cylinderMass src, audit.report.2 - cylinderMass src) :=
  audit_report_delta_of_open_iff audit (addCertificate audit src cert) hsub hfresh
    (fun m hm => addCertificate_open_iff audit src cert m hm)

/-- At the global root the containment premise is automatic. -/
theorem addCertificate_global_report_of_open {good : Machine → Prop}
    (audit : FrontierAudit good emptyTable) (src : PartialMachine) (cert : Cover good src)
    (hfresh : ∀ m, compatible src m → audit.open m) :
    (addCertificate audit src cert).report =
      (audit.report.1 + cylinderMass src, audit.report.2 - cylinderMass src) :=
  addCertificate_report_of_open audit src cert (fun m _ => empty_compatible m) hfresh

/-- A single conflicting fixed slot is enough to prove that two source
    cylinders are disjoint, with no traversal of their completions. -/
theorem incompatible_of_slot_conflict {p q : PartialMachine} (s : Slot)
    (t u : Transition) (hp : p s = some t) (hq : q s = some u) (hne : t ≠ u)
    (m : Machine) (hm : compatible p m) : ¬ compatible q m := by
  intro hqm
  exact hne ((hm s t hp).symm.trans (hqm s u hq))

#print axioms graftCertificate_report_of_extends
#print axioms addCertificate_report_of_open
#print axioms addCertificate_global_report_of_open
#print axioms incompatible_of_slot_conflict

end BB6Coverage
