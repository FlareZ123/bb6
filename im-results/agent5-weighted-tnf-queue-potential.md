# A well-founded potential for the pinned first-hole queue

**Status:** conditional algorithmic lemma grounded in the pinned upstream source. This is not a BB(6) upper-bound proof and does not certify the computed holdout roster.

## Exact queue semantics

The pinned source is ccz181078/busycoq, file verify/Enumerate62.v, revision 33209bc7dc282b38c8cd6be507bfc551fea56108. Its SearchQueue is a pair q=(q1,q2):

- q1=fst q is the active queue;
- q2=snd q is the holdout list.

For q1=x::q1', SearchQueue_upd applies the decider:
- Halt h: q1 becomes expand' x h ++ q1', q2 is unchanged;
- NonHalt: x is dropped from q1;
- Unknown: x is dropped from q1 and moved to q2.

The source's expand x h has two parts. For each existing state q in firstn m all_qs it creates four ordinary transitions (two writes and two directions); it also creates four transitions to the least fresh state q_m when one exists. Thus there are 4(m+1) children when m<6, and 24 when m=6: at most **28** children. Every child has num_undef_trans = Nat.pred n. The wrapper expand' returns [] when n=1, so no child is produced at the final hole.

The holdout list q2 is not processed by SearchQueue_upds. Unknown transfers a node out of the active queue; later chunk processing accumulates it in q2.

## Potential on the active queue

Let n(x)=x.num_undef_trans and define
[
\Phi(q)=\sum_{x\in\mathrm{fst}(q)}29^{n(x)}\in\mathbb N.
]

Every SearchQueue_upd step with a nonempty active queue strictly decreases this potential:

- Halt: remove the term 29^n and add at most 28 terms 29^(n-1), whose sum is strictly smaller because 28*29^(n-1) < 29^n.
- NonHalt: remove the positive term 29^n.
- Unknown: remove the positive term 29^n from q1. Do **not** include q2 in the potential: the Unknown node is transferred there unchanged.

Consequently, if SearchQueue_upds is allowed to continue until q1 is empty, it must empty after finitely many updates. More quantitatively, the number of updates is at most the initial active-queue potential.

## Connection to the fixed MAXT budget

The source defines MAXT=2^60 and computes holdout_i l sz by running SearchQueue_upds decider (q_i l sz) MAXT, where q_i takes a chunk of the finite q0 active list and preserves q0's prior holdouts.

Thus the potential gives a concrete route to proving that each holdout_i chunk was fully processed: prove
[
\Phi(q_i(l,sz))\le2^{60}
]
for every actual chunk. Then the active queue must empty before the MAXT fuel expires, and the resulting q2 contains every Unknown node from that chunk.

The crude worst-case bound for a chunk of 100 nodes with n≤11 is 100*29^11, which is slightly larger than 2^60 and therefore insufficient. If every node in a chunk has n≤10, the crude bound 100*29^10 is already below 2^60. The useful next computation is the exact per-chunk potential (or a tighter histogram bound) from q0, not another arbitrary runtime increase.

The four BFS passes defining q0 use SearchQueue_upd_bfs and SearchQueue_rst. In that variant, Unknown nodes are moved to q2 and then requeued by the reset; the above strict-decrease argument applies directly to the subsequent non-BFS SearchQueue_upds used by holdout_i, not to the total q1+q2 mass during a BFS pass.

## What remains unproved

This establishes only a conditional queue-termination bound. It does not by itself prove:

1. that the source's computed q0 is the exact frontier intended by the root expansion;
2. that each actual chunk's potential is at most MAXT;
3. that SearchQueue_upd preserves a coverage invariant over all compatible total machines;
4. that the decider's Halt and NonHalt answers are sound in the required source semantics;
5. that the resulting holdout list has been completely classified.

The local expansion-coverage obligation is the one represented by WeightedTNFCertificate.expand: every compatible total machine at a first hole is either in the halt case (discharged by the explicit weighted halt bound) or one of the canonical ordinary children. The queue proof must connect the pinned source's expand/expand' cases to this formal branch family, and separately prove soundness of decider classifications.

## Suggested formalization

1. Import or faithfully model the exact TNF_Node.T, SearchQueue, SearchQueue_upd and expand' definitions.
2. Prove a local lemma that every expand' child has one fewer undefined slot and that the child count is at most 28.
3. Prove strict decrease of Phi(fst q) for each nonempty SearchQueue_upd case.
4. Extract the exact n(x) histogram or exact Phi value for each q_i chunk and prove it is at most MAXT.
5. Prove the independent queue coverage invariant, using the weighted TNF branch theorem for Halt expansions and source-certified decider correctness for NonHalt/Halt classifications.

Termination and exhaustiveness are distinct: the potential addresses only the former.
