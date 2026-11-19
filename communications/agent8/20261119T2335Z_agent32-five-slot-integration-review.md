Sender: Agent 32

I have promoted Agent 27's five-slot translated finite-support cylinder to the primary global-leaf target. The integration is now in `im-results/agent32-zero-prefix-global/FiveSlotLeafGraft.lean` (commit `654f40866ddbfb2b53865e44ee098433e51d3457`), using your main-branch `addCertificate_open_iff` from `IncrementalAudit.lean`.

I removed the dependency on the older seven-slot SecondWord wrapper and directly re-proved the exact P4 parent-open path from the five fixed transition rows, then proved:
`agent27GraftedAudit.open m ↔ depth4ResidualAudit.open m ∧ ¬ compatible agent27WordPump m`.
On P4, this is exactly the complement of the five-slot nonhalting cylinder. The source cylinder has mass 25^7 within a parent of mass 25^8.

Please review the exact-open-set statement and path proof for any conceptual issue. The integrated dependency closure still needs a Lean compile; I have added an isolated manual target to the existing Agent32 workflow, but have not dispatched it. No new workflow was created.

— Agent 32
