# A well-founded potential for the pinned first-hole queue

**Status:** source-grounded algorithmic result about the pinned queue's fuel bound. It does not prove the queue's machine-coverage invariant or the BB(6) upper bound.

## Exact queue semantics

The pinned source is ccz181078/busycoq, file verify/Enumerate62.v, revision 33209bc7dc282b38c8cd6be507bfc551fea56108. Its SearchQueue is a pair q=(q1,q2):

- q1=fst q is the active queue;
- q2=snd q is the holdout list.

For q1=x::q1', SearchQueue_upd applies the decider:
- Halt h: q1 becomes expand' x h ++ q1', q2 is unchanged;
- NonHalt: x is dropped from q1;
- Unknown: x is dropped from q1 and moved to q2.

The BFS variant SearchQueue_upd_bfs has the same classification behavior, except Halt children are appended to q2 for the current pass; SearchQueue_rst then merges q1 and q2 into the next active queue. Unknown also moves x from q1 to q2 and is requeued by the reset.

The source's expand x h has two parts. For each existing state q in firstn m all_qs it creates four ordinary transitions (two writes and two directions); if m<6, it also creates four transitions to the least fresh state q_m. Therefore the number of children is
[
4m+4\quad(m<6),\qquad24\quad(m=6),
]
so the exact maximum is **24**. Every child has num_undef_trans = Nat.pred n. The wrapper expand' returns [] when n=1. Under the source node invariant, Halt h identifies an undefined slot, so n≥1.

## Potential on a queue

Let n(x)=x.num_undef_trans and define the total queue potential
[
\Phi(q)=\sum_{x\in\mathrm{fst}(q)}25^{n(x)}
       +\sum_{x\in\mathrm{snd}(q)}25^{n(x)}\in\mathbb N.
]

Every SearchQueue_upd_bfs step is nonincreasing for this total potential:

- Halt: remove the term 25^n and add at most 24 terms 25^(n-1), whose sum is strictly smaller because 24*25^(n-1)<25^n; if n=1, expand' adds no children.
- NonHalt: remove the positive term 25^n.
- Unknown: transfer the term from q1 to q2 unchanged.

SearchQueue_rst preserves the total potential because it only moves q2 entries into q1. Since root_1RB has one node with 11 undefined slots, its initial potential is exactly
[
\Phi(root\_1RB)=25^{11}=2,384,185,791,015,625.
]
Therefore the q0 frontier after four BFS passes satisfies
[
\Phi(q_0)\le25^{11}.
]

## MAXT cannot truncate any q_i call

For any l and sz, fst(q_i(l,sz)) is a sublist of fst(q0), and snd(q_i(l,sz))=snd(q0). In particular, the active-queue potential at the start of any q_i call is at most
[
\sum_{x\in\mathrm{fst}(q_i)}25^{n(x)}
\le\Phi(q_0)\le25^{11}.
]

Now consider the non-BFS SearchQueue_upds used by holdout_i. Its active-queue potential (counting only q1) strictly decreases at every update:

- Halt: replace x by at most 24 children with one fewer undefined slot, or by no children when n=1;
- NonHalt: drop x;
- Unknown: drop x from q1 and move it to q2, which is not counted in the active potential.

Thus q1 must empty in at most 25^11 updates, regardless of the chunk size sz. The source uses
[
\texttt{MAXT}=2^{60}=1,152,921,504,606,846,976,
]
and
[
25^{11}=2,384,185,791,015,625<2^{60}.
]
So MAXT is more than sufficient for **every** holdout_i(l,sz) call on a q0 chunk; no assumption that sz≤100 is needed. This closes the fuel-truncation concern for the source-defined chunk processing.

## The independent coverage invariant

For a fixed weighted bound B, define Good_B(m) to mean WeightedBound B m. A natural frontier invariant for a queue q=(q1,q2) is:

> Every total completion m of the initial root is either Good_B(m), compatible with some node in q1, or compatible with some node in q2.

The three SearchQueue_upd cases preserve this invariant, provided the imported decider and local branch lemmas are used correctly:

- **Halt h:** the source TC theorem supplies a run from the blank configuration to the first undefined/halting slot h. A completion assigning halt at h is a solved halter; combine the exact run length with the firstOne possible-delay bound to show Good_B. A completion assigning an ordinary instruction at h belongs, up to canonical fresh-state relabeling, to one of the children in expand' x h. If n=1, expand' is empty and every ordinary completion has no remaining halt row, hence is nonhalting.
- **NonHalt:** the relevant source theorem must show that every compatible completion is nonhalting, so the entire cylinder is Good_B.
- **Unknown:** move x from q1 to q2 unchanged; compatibility, and therefore the invariant, is preserved.

The child-coverage step in the Halt case is exactly the mathematical content of WeightedTNFCertificate.expand/tnf_branch_sound: all 24 ordinary instructions are covered, with fresh labels quotiented by state symmetry, while the halt choice is handled separately. The n=1 empty-expansion case is the last-hole argument.

Induction over SearchQueue_upds preserves the invariant for any finite fuel. The potential result additionally proves that every q_i active queue is actually empty before MAXT. If the q_i chunks partition fst(q0) and carry snd(q0) forward without omission or duplication, the final holdout list is therefore exhaustive relative to q0. To close the root, one must then classify every holdout or provide a weighted certificate for it.

## Upstream scope warning

The pinned upstream README (https://github.com/ccz181078/busycoq/blob/33209bc7dc282b38c8cd6be507bfc551fea56108/README.md) reports about 607 BB(6) holdouts and explicitly says the correctness of its TNF enumeration has not been proved in Rocq. It also says the individual-proof and decider pipeline over that enumeration is not part of the ordinary make build because the run is estimated to take about a month. Therefore the existence of the 607-entry holdout roster is not itself an exhaustive BB(6) certificate. The potential above proves the fixed MAXT fuel is sufficient; the missing enumeration-coverage theorem remains real.

## What remains unproved

The fuel-sufficiency result does **not** by itself prove:

1. that the external holdout roster is the union of all holdout_i outputs for a complete partition of fst(q0);
2. that SearchQueue_upd preserves the required coverage invariant over all compatible total machines;
3. that every decider Halt/NonHalt classification is used with its source theorem and the correct score accounting;
4. that the zero-prefix normalization and the upstream root_1RB queue together cover every six-state two-symbol machine.

The queue proof must connect the pinned source's expand/expand' cases to the Lean weighted TNF branch family, and separately prove source decider soundness and the chunk partition.

## Suggested formalization

1. Import or faithfully model the exact TNF_Node.T, SearchQueue, SearchQueue_upd, SearchQueue_upd_bfs, SearchQueue_rst and expand' definitions.
2. Prove the exact child-count bound 24 and that each child has one fewer undefined slot; handle n=1 separately.
3. Prove nonincrease of total potential for BFS updates and resets, then derive Phi(q0)≤25^11.
4. Prove strict decrease of the active-queue potential for each non-BFS SearchQueue_upd case; derive the MAXT bound for every q_i call.
5. Prove the independent queue coverage invariant, using the weighted TNF branch theorem for Halt expansions and source-certified decider correctness for NonHalt/Halt classifications.
6. Recover and prove the actual q_i chunk partition used to construct the external holdout roster.

The MAXT fuel bound now has a short, source-faithful proof independent of chunk size. Coverage and source-faithful interpretation remain the decisive logical obligations.
