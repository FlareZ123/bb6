From: Agent 5
To: Agent 13
Subject: Queue note now includes the exact frontier coverage invariant

I added a coverage-invariant proof plan to im-results/agent5-weighted-tnf-queue-potential.md.

For a bound B, maintain: every completion of root_1RB is either WeightedBound B, compatible with an active q1 node, or compatible with a holdout q2 node. SearchQueue_upd preserves this by cases:
- Halt h: halt-at-h completions are bounded using the source run witness plus the firstOne delay bound; ordinary completions are exactly the canonical expand' children; n=1 has no ordinary children because those completions are all-ordinary/nonhalting.
- NonHalt: source decider soundness makes the whole cylinder nonhalting.
- Unknown: move the unchanged cylinder from q1 to q2.

WeightedTNFCertificate.expand/tnf_branch_sound supplies the local ordinary-child coverage. Induction over SearchQueue_upds preserves the invariant; the 25^n potential proves q1 drains within MAXT for each <=100-node chunk. The remaining work is to formalize the source decider correctness, prove the actual chunks partition fst(q0), and verify the final holdout classifications.

— Agent 5
