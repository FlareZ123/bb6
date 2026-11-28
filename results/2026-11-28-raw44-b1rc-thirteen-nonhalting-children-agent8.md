# Source-certified thirteen nonhalting Raw44 B1=0RC children

**Status: original-source Lean accepted.** Workflow run [46141410917](https://github.com/FlareZ123/bb6/actions/runs/46141410917), job [140967958387](https://github.com/FlareZ123/bb6/actions/runs/46141410917/job/140967958387), compiled the complete source closure on repository revision `d7b284ba00689b5aa8090bcb633cc03ab0508693` with Lean 4.36.0-rc2. The final declarations use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or `native_decide` appears.

## Exact cylinders

Fix the Raw44 prefix
```text
A0=1RB, B0=1RC, B1=0RC, C0=0RD, D0=1LD, D1=1LB.
```

For each of the following thirteen distinct assignments to C1,
```text
0LB, 0LC, 0LD, 0RB, 0RC, 0RD,
1LA, 1LB, 1LC, 1LD, 1RB, 1RC, 1RD
```
leave the five entries A1, E0, E1, F0, F1 arbitrary. The source file
[`Raw44B1RC13Cycles.lean`](../im-results/agent16-raw44/Raw44B1RC13Cycles.lean)
defines the corresponding partial machines `p0` through `p12` and proves

```lean
BB6.Agent16Raw44Easy13.never0  ... never12
BB6.Agent16Raw44Easy13.cover0  ... cover12
```

where every `never_i` states that **every complete machine compatible with that five-hole child is nonhalting from the blank tape**. The proof for each child is a checked translated side-cycle certificate via the repository's `zipCycle_sound` theorem, rather than a finite-runtime extrapolation.

Each child contains exactly `25^5 = 9,765,625` complete standard machines. Because the thirteen children have different fixed C1 actions, they are pairwise disjoint. Therefore this single accepted family classifies

```text
13 × 25^5 = 126,953,125
```

complete Raw44/B1=0RC machines as nonhalting.

## Significance and boundary

This is a proof-bearing reduction of the Raw44 frontier: thirteen C1 branches under B1=0RC are closed for **all** assignments of their five remaining rows. It combines cleanly with separately source-certified whole-child Covers such as C1=0RF and with future C1 child proofs.

It is not a complete Raw44 parent Cover and does not by itself change the current global canonical residual count or prove a universal BB(6) upper bound. The remaining C1 choices under B1=0RC require their own source-certified children or a stronger parent-level argument.
