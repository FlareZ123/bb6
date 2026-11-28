# Raw139 D1=0RD: exact two-level residual frontier

## Result

Let `p` be the normalized Raw139 partial machine represented by

`[7,24,11,24,14,24,24,13,24,24,24,24]`

under the repository's ordinary transition-code convention.  This is the D1=0RD
cylinder studied in `im-results/agent6-raw139-d1-zeroRD/D1ZeroRD.lean`.

The first exact split leaves nine D0 children:
`[2,6,8,9,10,16,17,18,19]`.  Each of those nine children now has a
kernel-checked next-hole reduction.  Across the resulting second-level TNF actions there
are 196 admissible actions, of which 94 are discharged immediately by exact translated
cycle certificates.  The remaining **102** actions are represented explicitly by
`BB6.Agent6D1SecondLevelFrontier.frontier`.

The principal theorem is:

```lean
theorem BB6.Agent6D1SecondLevelFrontier.cover_of_frontier
    (B : Nat) (hB : 14 ≤ B)
    (h : ∀ p ∈ frontier, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) BB6.Agent6D1ZeroRD.p
```

and the exact cardinality theorem is

```lean
theorem BB6.Agent6D1SecondLevelFrontier.frontier_length :
    frontier.length = 102
```

Thus, for every weighted bound `B ≥ 14`, proving the 102 explicit residual partial
machines suffices to prove the whole normalized D1=0RD cylinder.

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

## Source-certified follow-on closures at weighted bound 3000

Three residual children of the D0=8 family are now fully certified and consumed:
C1 codes 1, 3, and 6.  The corresponding retained child artifacts are **15260696627**,
**15260299839**, and **15260935299**.  The composed theorem
`BB6.Agent6D1EightFive.cover` is source-accepted by CI
[46138910273](https://github.com/FlareZ123/bb6/actions/runs/46138910273), artifact
**15260876687** (SHA-256
`64e1e1ff4c7d2359871cccaa9cbfc3e0014b7cd65b37d229ef2a3534d8b50b5e`).
It reduces the complete D0=8 cylinder at weighted bound 3000 to only the five child
codes `[2,16,17,18,19]`.

Two residual children of D0=9, C1 codes 2 and 6, have likewise completed their entire
kernel joins in retained artifacts **15260522869** and **15260548085**.  Their compile
logs end in `FINAL 126 0 []` and `FINAL 118 0 []`, and the exported Covers use
only `[propext, Classical.choice, Quot.sound]`.  The original matrix jobs were marked
failed only after those proofs, by a subsequently corrected shell-variable assertion.
`D1NineFour.lean` consumes these two proofs and leaves codes
`[16,17,18,19]`; this composition remains pending independent source-gate acceptance
at the time of this result update.

These follow-on closures solve five of the 102 explicit second-level obligations at
weighted bound 3000.  The source module `D1SecondLevel97.lean` expresses the resulting
97-machine conditional frontier, but that stronger wrapper should be treated as pending
until its independent source gate succeeds.

## Scope

This is a strict reduction theorem for one normalized Raw139 subcylinder.  It does not
claim that the 102 frontier machines are all solved, does not prove a complete Raw139
parent Cover, and does not determine BB(6).  Its contribution is to replace the previous
nine opaque first-level obligations by an exact, kernel-checked, machine-explicit
second-level frontier on which independent solvers can work without reconstructing the
split.
