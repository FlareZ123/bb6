# Cut-sensitive potential for the Enumerate62 TNF queue

**Status: intermediate Lean extension; source-projection compile pending.** This sharpens the queue-work bound in Agent 48's `Enumerate62Potential.lean`. It is not a machine-classification result and does not prove the BB(6) upper bound.

## Exact recurrence

The pinned source's normalized expansion at cut (c) has:

- (4c) ordinary children targeting existing labels (q<c); their cut remains (c);
- four ordinary children targeting the least fresh label (q=c), when (c<6); their cut becomes (c+1);
- no fresh child at (c=6).

Every child has one fewer undefined row. When one hole remains, `expand'` returns no ordinary children.

Define the exact worst-case descendant-update count (W(c,n)) by

[
W(c,0)=W(c,1)=1,
]

and, for (n\ge2),

[
W(c,n)=
\begin{cases}
1+4cW(c,n-1)+4W(c+1,n-1),&c<6,\\
1+24W(6,n-1),&c=6.
\end{cases}
]

The leading 1 counts processing the current node. The recurrence is exact for the projected full expansion tree: old-label children retain the cut, while fresh-label children increase it. Consequently, a Halt update replaces a node's weight by exactly (W(c,n)-1); NonHalt and Unknown remove a positive active weight. The BFS update transfers Unknown nodes to holdout, and reset preserves total mass.

## Improved bounds

The root node has ((c,n)=(2,11)). The Lean recurrence computes

[
W(2,11)=3,072,847,418,605
]

instead of the coarser (25^{11}=2,384,185,791,015,625), an improvement by a factor of about 776.

For any projected node with seven holes,

| Cut (c) | (W(c,7)) |
|---:|---:|
| 0 | 888,933 |
| 1 | 3,810,329 |
| 2 | 13,980,909 |
| 3 | 43,268,961 |
| 4 | 108,653,749 |
| 5 | 199,411,801 |
| 6 | 199,411,801 |

Thus the seven-hole per-node bound is at most 199,411,801, versus (25^7=6,103,515,625), about 30.6 times smaller.

The proof in `CutSensitivePotential.lean` establishes:
1. exact child-mass equality for the projected source expansion;
2. strict decrease of active cut-mass under every nonempty queue update;
3. nonincrease of total cut-mass under each BFS round;
4. (\operatorname{cutMass}(q_0)\le W(2,11));
5. every `q_i`-style chunk drains before `MAXT=2^{60}), using the sharper bound.

The queue-work bound is therefore substantially tighter without changing the source schedule or relying on a guessed chunk size.

## Scope and remaining obligations

This is a Lean proof over Agent 48's `(holes,cut)` projection of the pinned `Enumerate62.v` expansion. It still requires the exact projection to be connected to the source Coq definitions in a source-accepted closure. It does **not** establish:

- the queue-coverage invariant over all compatible total machines;
- soundness of the actual source decider classifications;
- completeness of the external `holdout_i` roster or its chunk partition;
- weighted certificates for every final holdout;
- a universal upper bound or the exact value of BB(6).

The point is narrower but useful: the worst-case queue-work accounting can track the number of already introduced states, rather than charging every level as if all 24 branches remained available. Keep this under `im-results/` until the source bridge and acceptance are complete.
