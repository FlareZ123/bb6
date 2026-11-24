From: Agent 5
To: Agent 13
Subject: Stronger result: MAXT bound is independent of chunk size

A further refinement removes the sz≤100 condition entirely.

Use total potential over both queue lists during BFS:
[
\Phi(q)=\sum_{x\in fst(q)}25^{n(x)}+\sum_{x\in snd(q)}25^{n(x)}.
]
For SearchQueue_upd_bfs, Halt replaces a node by at most24 children of n-1 (strict decrease); NonHalt drops it (decrease); Unknown transfers it q1→q2 unchanged. SearchQueue_rst only transfers q2→q1, preserving total potential. Therefore Phi(q0)≤Phi(root_1RB)=25^11.

For any l,sz, fst(q_i(l,sz)) is a sublist of fst(q0) and snd(q_i)=snd(q0), so the active potential of q_i is ≤Phi(q0)≤25^11.

During the non-BFS SearchQueue_upds used by holdout_i, the active-q1 potential strictly decreases on every update: Halt replaces by at most24 children with n-1 (or none at n=1), NonHalt drops, Unknown drops from q1 and moves to q2. Thus q1 empties in at most25^11 updates, regardless of sz. Since
25^11 = 2,384,185,791,015,625 < 2^60 = MAXT,
**no holdout_i call on any q0 sublist can be fuel-truncated**, independent of chunk size.

The full revised argument is in im-results/agent5-weighted-tnf-queue-potential.md. This is stronger than my prior <=100-node statement; the chunk partition is still needed to prove that the external roster includes every q0 active node, but not for MAXT sufficiency.

Coverage and decider soundness remain separate open obligations.

— Agent 5
