# Recurrent obstructions in the 211-state paired-carry subset automaton

**Status:** exact finite-automaton structural result. This is not an invariant for the authentic #623 root digit stream and does not prove #623 nonhalting.

## Construction and independent transition check

The base machine is the 66-state paired-carry closure in `../agent49-parity623/PostResetCarryPairClosure.json`. The 211-state machine in `PairCarrySynchronizingSubsetDFA.json` is its image-subset automaton, starting from the full 66-state set. A subset is a singleton exactly when the suffix transformation has rank one and has synchronized all 66 possible post-reset carry states.

I independently reconstructed every subset transition by applying the corresponding 66-state transition to every member of the subset and taking the image. All **1,899 transitions** (211 states × 9 symbols) agree exactly; there are zero mismatches.

## Exact SCC partition

The 211 states split as follows:

| Class | States | Meaning |
|---|---:|---|
| One recurrent SCC of singleton subsets | 66 | Fully synchronized; rank one |
| Transient nonsingleton states | 62 | Cannot support an infinite nonsynchronizing path |
| Recurrent nonsingleton SCCs | 10 components / 83 states | The only possible infinite obstructions |

The condensation graph gives a sharp finite prefix bound: from the initial full 66-state subset, every input path reaches either a singleton subset or one of the ten recurrent nonsingleton components within **at most four symbols**. A longest transient witness is symbol IDs `2,6,0,2`, i.e. digit pairs `(0,2),(2,0),(0,0),(0,2)`, reaching the 30-state component whose R projection is singleton.

The full machine has 73 SCCs, with component-size histogram `1:65, 2:1, 4:3, 6:1, 30:2, 66:1`.

## The ten recurrent nonsynchronizing components

Symbol encoding is `3*x+y).

| Component | States | Subset size | Branch projection | Exact internal language |
|---|---:|---:|---|---|
| B1 | 30 | 2 | L: 2 states; R: 1 | At each state exactly one x digit is allowed, with all three y digits |
| B2 | 30 | 2 | L: 1 state; R: 2 | At each state exactly one x digit is allowed, with all three y digits |
| B3 | 4 | 4 | L: 2; R: 2 | Periodic 4-cycle |
| B4 | 1 | 3 | L: 1; R: 3 | Fixed symbol `(0,2)` |
| B5 | 6 | 2 | L: 1; R: 2 | Only `(0,2),(1,1),(2,0)`, so `x+y=2` |
| B6 | 1 | 4 | L: 2; R: 2 | Fixed symbol `(1,1)` |
| B7 | 1 | 3 | L: 1; R: 3 | Fixed symbol `(2,0)` |
| B8 | 2 | 4 | L: 2; R: 2 | Periodic 2-cycle |
| B9 | 4 | 3 | L: 2; R: 2 | Periodic 4-cycle |
| B10 | 4 | 3 | L: 2; R: 2 | Periodic 4-cycle |

The two 30-state components are carry-ambiguity systems: every state has three internal edges, their x-coordinate is fixed at that state, and y may be 0, 1, or 2. The six-state component is even simpler: every internal symbol satisfies (x+y=2). The other seven components are three 4-cycles, one 2-cycle, and three fixed-symbol loops. Exact state IDs, transition edges, carry projections, and cycle words are in [`NonSynchronizingSCCs.json`](NonSynchronizingSCCs.json).

Across the 83 recurrent nonsingleton states, the branch-projection histogram is:

- `1/2`: 36 states (L projection singleton, R projection has two states);
- `1/3`: 2 states (L singleton, R has three states);
- `2/1`: 30 states (L has two states, R singleton);
- `2/2`: 15 states (both projections remain ambiguous).

Thus 68 of the 83 recurrent nonsingleton states still determine one entire branch projection. This is a useful branch-sensitive refinement, but it is not by itself a root theorem: the authentic source branch must be composed with the exact S-window own-start phase.

## What this reduces

An infinite suffix that fails to synchronize all 66 paired-carry states cannot wander indefinitely through arbitrary subset states. After at most four symbols it must remain in one of the ten explicit recurrent components above. The remaining source-level problem is therefore to show that the authentic S-window digit-pair stream cannot eventually follow any of these ten component languages, or to show that the root's active branch is already determined on every reachable product state.

The next product must retain the distinction between:

1. the source-to-target carry used to validate the current output interval; and
2. the target state's own-start carry, recomputed from that target's own drain statistics and correction for the next transition.

Do not substitute the 1,318 finite source-to-target transition keys for the own-start phase set. Also retain the full universal L/R carry rectangles until a common reset has actually been witnessed.

## Reproduction

From the repository root:

```sh
node im-results/agent27-623-root-scan/analyze_non_sync_sccs.js
```

The script reconstructs the 211-state transition relation from the 66-state closure, computes the SCCs, verifies the exact partition and four-symbol transient bound, and writes `NonSynchronizingSCCs.json`.
