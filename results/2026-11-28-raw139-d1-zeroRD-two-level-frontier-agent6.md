# Raw139 D1=0RD: certified 102-to-96 residual frontier

## Strongest source-accepted theorem

Let `p` be the normalized Raw139 D1=0RD partial machine
`[7,24,11,24,14,24,24,13,24,24,24,24]` under ordinary transition codes.
At weighted bound `B≥3000`, the strongest accepted conditional theorem is

```lean
theorem BB6.Agent6D1SecondLevel96Bound.cover_of_frontier
    (B : Nat) (hB : 3000 ≤ B)
    (h : ∀ p ∈ BB6.Agent6D1SecondLevel96.F.frontier,
      Cover (WeightedBound B) p) :
    Cover (WeightedBound B) BB6.Agent6D1ZeroRD.p
```

The explicit frontier has exactly **96** members: `frontier_length = 96`.
This bound-uniform result source-compiled with Lean 4.36.0-rc2 in
[run 46147351683](https://github.com/FlareZ123/bb6/actions/runs/46147351683),
artifact **15264817299**, digest
`sha256:b98a54edefd073cbdc295d6543c4ab3db638a5c9a70d30e6788997e964265da4`.
The check audits six separately accepted complete child Covers and the complete
transitive source closure; exported Cover theorems depend only on
`[propext, Classical.choice, Quot.sound]` with neither `sorryAx` nor
`ofReduceBool`.

The original `D1SecondLevelFrontier.cover_of_frontier` still gives a stronger
*threshold* (`B≥14`) but needs **102** explicit grandchildren:
```lean
theorem BB6.Agent6D1SecondLevelFrontier.cover_of_frontier
    (B : Nat) (hB : 14 ≤ B)
    (h : ∀ p ∈ frontier, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) BB6.Agent6D1ZeroRD.p
```
All nine D0 first-level hard children have exact next-hole reductions.
Across 196 admissible second-level actions, 94 terminate in
source-checked translated-cycle Covers; the other 102 form the original
frontier. The 96 theorem consumes six additional whole grandchildren at
weighted 3000 and uses Cover monotonicity to preserve the result for all
larger bounds.

## Exact second-level partition

| D0 code | next queried slot / ordinary step | remaining action codes | count |
| --- | --- | --- | ---: |
| 2 | A1 / 7 | `[0,2,6,8,9,10,15,16,17,18,19]` | 11 |
| 6 | C1 / 7 | `[0,2,4,6,9,15,16,17,18,19]` | 10 |
| 8 | C1 / 8 | `[1,2,3,6,16,17,18,19]` | 8 |
| 9 | C1 / 8 | `[2,6,16,17,18,19]` | 6 |
| 10 | C1 / 8 | `[0,1,2,3,5,6,7,16,17,18,19]` | 11 |
| 16 | E0 / 6 | `[2,6,9,12,14,15,16,18,20,21,22,23]` | 12 |
| 17 | E0 / 6 | `[2,6,8,9,10,14,16,18,20,21,22,23]` | 12 |
| 18 | E0 / 6 | `[0,1,2,3,5,6,7,9,11,12,14,16,17,18,19,20,21,22,23]` | 19 |
| 19 | E0 / 6 | `[0,2,4,6,8,9,10,16,18,20,21,22,23]` | 13 |

The five cut-4 children contribute 100 admissible actions and the four cut-5 children
contribute 96, for 196 total.  The hard counts sum to 102, hence 94 actions are closed
locally by the reducer cycle certificates.

## Formal sources

The nine exact reducers are in:

- `D1SixReduce.lean`;
- `D1EightReduce.lean`;
- `D1NineReduce.lean`;
- `D1LateD0Reduce.lean`;
- `D1RemainingD0Reduce.lean`;

all under `im-results/agent6-raw139-d1-zeroRD/`.

`D1SecondLevel.lean` composes those reducers through the first-level
`D1ZeroRD.cover` theorem.  `D1SecondLevelFrontier.lean` packages the residual
families into the explicit 102-element list and proves the theorem above.

Pinned source CI run
[46138720868](https://github.com/FlareZ123/bb6/actions/runs/46138720868)
checked every reducer, the two-level composition, the explicit frontier length, and
`cover_of_frontier` with Lean 4.36.0-rc2.  The retained artifact is
**15260946325**, digest
`sha256:f1414f86d5fcf02e8b7c2d31fdb8e9bd712d3ed81bc70313c4a837a7cafdc420`.
The exported Cover theorems depend only on
`[propext, Classical.choice, Quot.sound]`; the gate rejects `sorryAx` and
`ofReduceBool`.


## Fully consumed children and proof chain

At weighted 3000 the accepted complete second-level child Covers are:

| D0 / C1 code | Source evidence | Status |
| --- | --- | --- |
| 8 / 1,3,6 | Artifacts 15260696627, 15260299839, 15260935299; [D1EightFive join 46138910273](https://github.com/FlareZ123/bb6/actions/runs/46138910273) | Fully source accepted |
| 8 / 17 | [Run 46139905624](https://github.com/FlareZ123/bb6/actions/runs/46139905624), artifact 15262091078 | Fully source accepted; source `D1EightFour.c17` transports it |
| 9 / 2,6 | Artifacts 15260522869 and 15260548085; source consumer `D1NineFour` included in [run 46139540619](https://github.com/FlareZ123/bb6/actions/runs/46139540619) | Fully source accepted |

The five-child source-consumer `D1EightFive.cover` is accepted in
[run 46138910273](https://github.com/FlareZ123/bb6/actions/runs/46138910273).
The predecessor `D1SecondLevel97.cover_of_frontier` (five children
eliminated) is source accepted in
[run 46139540619](https://github.com/FlareZ123/bb6/actions/runs/46139540619),
artifact **15260783376**, digest
`sha256:dc7152ec7342dd11a7b6c8e87ceed83c1728d5ff9a8248b549a5726ada9ac795`.
The stronger `D1EightFour.cover` consumes the D0=8/C1=17 theorem, leaving
the four D0=8 C1 codes **[2,16,18,19]**. The D0=9 C1 complement remains
**[16,17,18,19]**. These eight grandchildren are among the 96 outstanding
second-level obligations.

The six child proofs are checked at weighted 3000; the theorem
`D1SecondLevel96Bound.cover_of_frontier` proves the uniform
`B≥3000` transport by structural induction on `Cover`, then applies
the original source-level first-hole reductions. The exact saved
source modules are `D1EightFour.lean`, `D1SecondLevel96.lean`, and
`D1SecondLevel96Bound.lean` in
[the ongoing formalization](../im-results/agent6-raw139-d1-zeroRD/README.md).

## Scope and open upper-bound edge

The source-proved theorems are strict reductions on **one** Raw139
subcylinder, not a complete Cover of the Raw139 parent. None resolves
the other 96 grandchildren or the universal BB(6) maximality bound.
All-completion parent certificates for D0=8 and D0=9 would eliminate
another eight of these 96 obligations and leave a conditional 88-machine
frontier; `D1SecondLevel88OfParents.lean` stages that latter statement
with **explicit hypotheses for both whole-parent Covers**, not accepted
full-parent results. The authentic long-arrival D0=2 branches require
bounds far above 3000; the bound-uniform interface is needed to integrate
them without falsely claiming a short stopping bound.
