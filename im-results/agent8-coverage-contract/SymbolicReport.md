# Symbolic frontier report certification

**Status:** locally compiled against copied source declarations (Lean 4.36.0-rc2, dependency-sliced Frontier/FrontierAudit/FrontierMass, full IncrementalAudit and corrected CertificateBatch). Standard axiom profiles only: propext, Classical.choice, Quot.sound; slot-conflict lemma axiom-free. Full unmodified repository dependency closure remains to be compiled. This is intermediate proof infrastructure, not a new holdout decision.

For a frontier with report (D,U), adding a source cylinder that lies entirely within the old open set changes the report exactly to (D + 25^k, U - 25^k), where k counts the free source slots. The proof constructs a finite raw-table measure via nested sums over the 12 slots and their 25 distinct choices; symbolic induction establishes its cylinder cardinality and disjoint additivity. A second induction over the audit shows the report coordinates equal the semantic certified and open event measures. No evaluation of the 25^12 full machines or of a concrete large audit is required.

- AuditReportMeasure.lean: audit_report_eq_of_open_iff, audit_report_delta_of_open_iff.
- IncrementalAuditReport.lean: graftCertificate_report_of_extends, addCertificate_report_of_open, addCertificate_global_report_of_open, incompatible_of_slot_conflict.
- ../agent27-three-slot-translated/CertificateBatchReport.lean: addCertificates_report_of_open and global-root version; certifies a finite batch with a single sum and pairwise disjointness premise.

The batch uses the existing CertificateBatch module, repaired to use a subtype (Cover is Prop, not Type) and associate conjunctions explicitly. No separate count is valid if a certificate overlaps already-decided mass or another source: the premises intentionally require entire source openness and pairwise disjointness. To use in P4, prove each candidate's compatibility implies openness in the baseline audit, prove pairwise slot conflicts, then reduce just the list of cylinder masses. Use the existing manual frontier workflow, not a new full-tree evaluation. The base report must be separately certified or carried as an explicit premise.
