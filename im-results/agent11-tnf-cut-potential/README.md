# Cut-sensitive potential for the Enumerate62 TNF queue

**Status: two Lean layers accepted; the source-Coq queue lift remains open.**

1. The projected queue potential in `CutSensitivePotential.lean` passed the existing `agent13-coverage.yml` `source-queue-adapter` target at [run 45451825548](https://github.com/FlareZ123/bb6/actions/runs/45451825548), head `4e0514a295135f1eabf3872c61418523e1fd4e32`.
2. The original Lean source-node bridge in `SourceNodeCutAdapter.lean` passed the same target at [run 45478573206](https://github.com/FlareZ123/bb6/actions/runs/45478573206), head `aca8f306466fc4622ccbf6ab5b1d4ad4155284a8`. The fail-hard `sorryAx|native_decide` scan passed.

These are Lean results. The second layer proves the per-child correspondence for the actual `Enumerate62Adapter.SourceNode`; it does **not** yet prove the complete Coq `expand` list's pair distribution or the Coq `SearchQueue_upd` mass theorem. No BB(6) upper bound is claimed.

## Exact recurrence

At cut (c), the projected expansion has:

- (4c) children targeting existing labels (q<c), retaining cut (c);
- four children targeting the least fresh label (q=c), raising the cut to (c+1), when (c<6);
- no fresh-label children at (c=6).

Every child has one fewer undefined row. When one hole remains, `expand'` returns no ordinary children.

Define the projected worst-case descendant-update count (W(c,n)) by

[
W(c,0)=W(c,1)=1,
]

and, for (nge2),

[
W(c,n)=
egin{cases}
1+4cW(c,n-1)+4W(c+1,n-1),&c<6,\\
1+24W(6,n-1),&c=6.
end{cases}
]

The leading 1 counts processing the current node. This recurrence is exact for Agent 48's ((holes,cut)) projection.

## Improved projected bounds

The projected root has ((c,n)=(2,11)):

[
W(2,11)=3,072,847,418,605,
]

versus the coarser (25^{11}=2,384,185,791,015,625), an improvement by a factor of about 776.

For seven-hole projected nodes:

| Cut (c) | (W(c,7)) |
|---:|---:|
| 0 | 888,933 |
| 1 | 3,810,329 |
| 2 | 13,980,909 |
| 3 | 43,268,961 |
| 4 | 108,653,749 |
| 5 | 199,411,801 |
| 6 | 199,411,801 |

Thus the projected seven-hole per-node bound is at most 199,411,801, versus (25^7=6,103,515,625), about 30.6 times smaller.

In `CutSensitivePotential.lean`, the Lean proof establishes:
1. exact child-mass equality for the projected expansion;
2. strict decrease of projected active cut-mass under each nonempty queue update;
3. nonincrease of projected total cut-mass under each BFS round;
4. projected (operatorname{cutMass}(q_0)le W(2,11));
5. every projected `q_i`-style chunk drains before `MAXT=2^{60}).

These bounds concern the projected queue model, not yet the original Coq queue.

## Original Lean source-node bridge

`SourceNodeCutAdapter.lean` imports the original Lean `Enumerate62Adapter` definitions and proves:

- `sourceNodeAsCutNode_cut`: under `SourceWF`, the projected cut is exactly the source node's least fresh state;
- `cutNodeWeight_sourceNode`: the source node's cut-sensitive weight is exactly (W(fresh,holes));
- `sourceChildAsCutNode`: every legal source child projects to the existing-label or least-fresh child;
- `cutNodeWeight_sourceChild`: its exact weight is (W(fresh,holes-1)) for an existing label and (W(fresh+1,holes-1)) for the fresh label.

The child theorem assumes an undefined source slot, a slot below the fresh-state frontier, and a destination no greater than that frontier. The CI target compiled the adapter and passed the placeholder/native-decision scan.

This closes the per-child Lean projection correspondence. It does not establish that the full original Coq `expand` list contains exactly (4c) old-label children and four fresh-label children, nor that the Coq queue's active/holdout mass follows this recurrence.

## Next source-level obligations

1. Prove the pair distribution ((num\_undef\_trans,min\_unused\_state)) for the actual Coq `expand` definition.
2. Define Coq `cutWeight`/`cutMass` and prove strict active-mass decrease for the actual `SearchQueue_upd`, plus total-mass monotonicity for BFS/reset.
3. Apply the source theorem to the actual (q_0) chunks and their cut-sensitive fuel bounds.
4. Independently complete classifier soundness, exhaustive holdout/roster coverage, and the universal machine upper bound.

The natural next artifact is an isolated `Agent11CutSource.v` importing the accepted `Agent32SourceDrain` and `Agent32Q0Partition` source modules, compiled by the existing `shared-rocq-root-proofs.yml` target. Keep this work under `im-results/` until the source-level proof and the global classification obligations are complete.
