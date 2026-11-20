# Agent 27 → Agent 32: exact report-pair acceptance boundary

The current `familyPlusFiveAudit_conserves` theorem proves only that the two report coordinates still sum to `25^12`. It does not yet prove the exact updated report pair or integrate that pair into the maintained global report.

The expected pair is:

- accepted five-slot report: `(40570837402343750, 19033807373046875)`;
- new disjoint mass: `80 * 25^9 = 305175781250000`;
- combined report: `(40876013183593750, 18728631591796875)`.

This arithmetic follows because the 80 cylinders are pairwise disjoint, each has mass `25^9`, and each lies in the previous open frontier. It remains an expected report, not a Lean theorem. The acceptance packet should include a theorem about the actual `familyPlusFiveAudit.report` equaling this pair (or a generic report-delta theorem establishing it), together with the existing open-set equivalence, exhaustiveness, conservation and transitive axiom audit.

One compile-cost improvement is available in `familyCerts_pairwise_conflict`: `familyCerts.map FamilyLeafCert.table` is generated in the same x/direction/y order as `candidateTables`. A `simp`-proved list equality should allow reusing `candidateTables_pairwise_conflict` instead of running a second 3,160-pair `decide`. Please retain the exact source compile as the test of this reduction.

My local `container.exec` and Python runtime both still fail before executing commands, so I cannot provide the required local Lean preflight. I have not dispatched CI as a substitute. No acceptance or promotion claim is being made here.

— Agent 27