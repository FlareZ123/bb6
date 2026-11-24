# Enumerate62 queue potential and MAXT fuel bound

**Intermediate formal result.**

**Lean acceptance:** Lean 4.36.0-rc2, manual CI run [45395870762](https://github.com/FlareZ123/bb6/actions/runs/45395870762), commit `20298b72972413484219a5de03736a22ea45244a`. The acceptance script compiles this module and checks the listed theorem axiom profiles; the run passed.

The proof is in [`Enumerate62Potential.lean`](Enumerate62Potential.lean).

## What is formalized

This is the potential-relevant projection of the `verify/Enumerate62.v` worklist. It erases the transition-table payload but retains the two node fields that determine the expansion potential:

- `holes`: `num_undef_trans`;
- `cut`: `min_unused_state`, represented by `Fin 7).

The expansion projection preserves the source multiplicities and metadata updates:

- (4m) children reuse one of the (m) existing labels and retain cut (m);
- if (m<6), four more children use the least fresh label (m+1);
- every child has (operatorname{pred}(n)) holes;
- `expand'` produces no ordinary children when (n=1).

The fresh-label theorem `freshChild_cut` confirms that the totalized modulo-7 representation is exactly (m+1) in the only branch where a fresh child is emitted.

Zero-hole nodes are allowed in the queue: a total machine may remain `Unknown`. The dependent `Verdict.halt` constructor carries the local proof (1le n) needed to invoke `expand'`; this avoids imposing an invalid positive-hole invariant on all holdout nodes.

## Potential argument

Assign each node the weight

[
W(x)=25^{operatorname{holes}(x)}
]

and each queue the sum of its node weights.

For a node with (nge2), the source expansion has at most 24 children, each with (n-1) holes. Therefore

[
sum_{yinoperatorname{expand'}(x)}W(y)
le 24cdot25^{n-1}
<25^n=W(x).
]

For (n=1), `expand'` is empty, so the same strict decrease holds. A non-BFS update strictly decreases active-queue mass for every possible decision: Halt replaces a node by lower-mass children, NonHalt removes it, and Unknown moves it to holdout.

A BFS pass processes exactly its initial active list, appends children/Unknown nodes to holdout, then resets holdout to active. Its total mass is nonincreasing. The root projection has 11 holes and cut 2, so its initial mass is (25^{11}). Four BFS passes therefore give

[
operatorname{mass}(q_0)le25^{11}.
]

Every source-style slice

[
q_i(l,s)=
igl(operatorname{take}(s,operatorname{drop}(l,q_0.active)),
q_0.holdoutigr)
]

has active mass at most the total mass of (q_0). Since each non-BFS update decreases active mass by at least one, (25^{11}) updates suffice to empty the active queue. The source fuel is (MAXT=2^{60}), and Lean proves (25^{11}le2^{60}).

The principal exported result is `BB6.Agent48Queue.every_chunk_drains`: for every source-style decider and every (l,s), the active queue of the corresponding slice is empty after (2^{60}) updates.

## Exact scope and remaining obligations

This discharges a **fuel-truncation** concern for the projected queue. It does not prove:

1. correctness or completeness of the decider;
2. that the projected queue is formally equivalent to the complete Coq queue implementation;
3. that all (q_i) chunks were actually scheduled;
4. the partition/coverage theorem for the external chunk schedule;
5. soundness of the final holdout roster or a weighted TNF certificate.

Agent 5 is working on the source adapter and chunk schedule/partition; Agent 13 is pursuing the generic queue-coverage invariant. Keep this result in `im-results/`: it is not an exact BB(6) proof and does not establish the required universal upper bound.
