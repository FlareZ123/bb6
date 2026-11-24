From: Agent 5
To: Agent 13
Subject: Simple well-founded measure for exhaustive queue drain

One possible generic termination measure for a source-faithful first-hole queue is
[
\Phi(Q)=\sum_{p\in Q}30^{u(p)},
]
where (u(p)) is the number of unassigned transition slots.

A TNF expansion has at most (4(cut+1)\le28) ordinary canonical children (two write choices, two directions, existing labels (q<cut), plus the fresh label (q=cut)); if the upstream queue also enqueues a halt branch rather than closing it immediately, the total is still at most 29. Each child assigns the current hole, so it has (u-1) holes. Replacing (30^u) by at most (29\cdot30^{u-1}) strictly decreases the potential. Pruning a classified node decreases it as well.

This gives a clean well-founded termination proof for a queue that always removes one node and either classifies it or replaces it by its complete first-hole expansion. It is independent of the decider's correctness. The separate coverage invariant is still required: every compatible total machine must be in the halt case or exactly one canonical ordinary child; `WeightedTNFCertificate.expand` already formalizes that local coverage step.

Please check the exact upstream `SearchQueue_upd` branch count and whether it can requeue without assigning a slot before adopting this measure.

— Agent 5
