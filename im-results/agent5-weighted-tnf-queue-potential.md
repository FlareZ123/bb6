# A well-founded potential for the pinned first-hole queue

**Status:** conditional algorithmic lemma grounded in the pinned upstream source. It closes the MAXT fuel-sufficiency issue for chunks of at most 100 nodes, but does not by itself prove global coverage or the BB(6) upper bound.

## Exact queue semantics

The pinned source is ccz181078/busycoq, file verify/Enumerate62.v, revision 33209bc7dc282b38c8cd6be507bfc551fea56108. Its SearchQueue is a pair q=(q1,q2):

- q1=fst q is the active queue;
- q2=snd q is the holdout list.

For q1=x::q1', SearchQueue_upd applies the decider:
- Halt h: q1 becomes expand' x h ++ q1', q2 is unchanged;
- NonHalt: x is dropped from q1;
- Unknown: x is dropped from q1 and moved to q2.

The source's expand x h has two parts. For each existing state q in firstn m all_qs it creates four ordinary transitions (two writes and two directions); if m<6, it also creates four transitions to the least fresh state q_m. Therefore the number of children is
[
4m+4\quad(m<6),\qquad24\quad(m=6),
]
so the exact maximum is **24**, not 28. Every child has num_undef_trans = Nat.pred n. The wrapper expand' returns [] when n=1, so no child is produced at the final hole.

The holdout list q2 is not processed by SearchQueue_upds. Unknown transfers a node out of the active queue; later chunk processing accumulates it in q2.

## Potential on the active queue

Let n(x)=x.num_undef_trans and define
[
\Phi(q)=\sum_{x\in\mathrm{fst}(q)}25^{n(x)}\in\mathbb N.
]

Every SearchQueue_upd step with a nonempty active queue strictly decreases this potential:

- Halt: if n>1, remove the term 25^n and add at most 24 terms 25^(n-1), whose sum is strictly smaller because 24*25^(n-1)<25^n. If n=1, expand' adds no children, so the term is removed.
- NonHalt: remove the positive term 25^n.
- Unknown: remove the positive term 25^n from q1. Do **not** include q2 in the potential: the Unknown node is transferred there unchanged.

Consequently, SearchQueue_upds must empty q1 after finitely many updates, with the number of updates bounded by the initial active-queue potential.

## The fixed MAXT budget is sufficient for 100-node chunks

The upstream root node0 has num_undef_trans=11. Every queue operation either:
- replaces a node by children with one fewer undefined slot;
- drops a node as NonHalt; or
- moves a node to q2 as Unknown.

The BFS reset may requeue Unknown nodes, but it does not increase their undefined-slot count. Therefore every node in q0, the frontier after four BFS passes, has n(x)≤11.

For any chunk of at most 100 q0 nodes,
[
\Phi(q_i(l,sz))\le100\cdot25^{11}
=238,418,579,101,562,500
<2^{60}
=1,152,921,504,606,846,976
=\texttt{MAXT}.
]
Thus, for every actual holdout_i call with sz≤100, the active queue must empty before the MAXT fuel expires. This proves that the chunk's holdout output is not truncated by the iteration budget. The exact q0 distribution is not needed for this bound.

The source defines holdout_i(l,sz) generically; its comments exhibit q_i(0,100). The conclusion is conditional on the actual external calls using chunks of size at most 100. If a larger sz was used, recompute the bound as sz*25^11.


## The independent coverage invariant

For a fixed weighted bound B, define Good_B(m) to mean WeightedBound B m. A natural frontier invariant for a queue q=(q1,q2) is:

> Every total completion m of the initial root is either Good_B(m), compatible with some node in q1, or compatible with some node in q2.

The three SearchQueue_upd cases preserve this invariant, provided the imported decider and local branch lemmas are used correctly:

- **Halt h:** the source TC theorem supplies a run from the blank configuration to the first undefined/halting slot h. A completion assigning halt at h is a solved halter; combine the exact run length with the firstOne possible-delay bound to show Good_B. A completion assigning an ordinary instruction at h belongs, up to the canonical fresh-state relabeling, to one of the children in expand' x h. If n=1, expand' is empty and every ordinary completion has no remaining halt row, hence is nonhalting.
- **NonHalt:** the relevant source theorem must show that every compatible completion is nonhalting, so the entire cylinder is Good_B.
- **Unknown:** move x from q1 to q2 unchanged; compatibility, and therefore the invariant, is preserved.

The child-coverage step in the Halt case is exactly the mathematical content of WeightedTNFCertificate.expand/tnf_branch_sound: all 24 ordinary instructions are covered, with fresh labels quotiented by state symmetry, while the halt choice is handled separately. The n=1 empty-expansion case is the last-hole argument.

Induction over SearchQueue_upds then preserves the invariant for any finite fuel. The potential result above additionally proves that, for chunks of at most 100 nodes, the active q1 is actually empty before MAXT. If the chunks partition fst(q0) and carry snd(q0) forward without omission or duplication, the final holdout list is therefore exhaustive relative to q0. To close the root, one must then classify every holdout or provide a weighted certificate for it.


## What remains unproved

The fuel-sufficiency result does **not** by itself prove:

1. that the external holdout roster is the union of all holdout_i outputs for a complete partition of fst(q0);
2. that SearchQueue_upd preserves the required coverage invariant over all compatible total machines;
3. that every decider Halt/NonHalt classification is used with its source theorem and the correct score accounting;
4. that the zero-prefix normalization and the upstream root_1RB queue together cover every six-state two-symbol machine.

The local expansion-coverage obligation is the one represented by WeightedTNFCertificate.expand: every compatible total machine at a first hole is either in the halt case (discharged by the explicit weighted halt bound) or one of the canonical ordinary children. The queue proof must connect the pinned source's expand/expand' cases to this formal branch family, and separately prove soundness of decider classifications.

## Suggested formalization

1. Import or faithfully model the exact TNF_Node.T, SearchQueue, SearchQueue_upd and expand' definitions.
2. Prove the exact child-count bound 24 and that each child has one fewer undefined slot; handle the n=1 empty expansion separately.
3. Prove strict decrease of Phi(fst q) for each nonempty SearchQueue_upd case.
4. Prove that every actual holdout_i call has sz≤100 (or use its exact sz) and derive the displayed MAXT inequality.
5. Prove the independent queue coverage invariant, using the weighted TNF branch theorem for Halt expansions and source-certified decider correctness for NonHalt/Halt classifications.

The fuel bound now has a short, explicit arithmetic proof. Coverage and source-faithful interpretation remain the decisive logical obligations.
