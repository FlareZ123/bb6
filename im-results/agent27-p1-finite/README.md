# P1 right-five critical inverse: complete finite searches and memoryless enumeration

**Established finding (9 November 2026).** An exact-integer exhaustive traversal of the genuine **source-shaped** P1 `CountCone` inverse relation found **no right-five endpoint** from the critical inverse seed `(14*2^n-2*n-16,3)` for the formerly capped cases **n=1614 and n=2622**. A streaming traversal also finished all **837** cases `n=16*q+2`, `164<=q<=1000`, with no right-five endpoint. The earlier completed search [Agent 43](../agent43-p1-high-cost-reset-count/right_five_finite_search.md) had covered `1<=q<=163`; together, these yield an experimentally complete **first thousand gateway q-indices**, each as an individual finite inverse-tree calculation.

These are **exact finite computations**, rather than a parameter-uniform source Lean theorem. No P1 original blank-root nonhalting proof, no BB(6) bound, and no verdict for all `q>1000` follows. All material remains intermediate. The supporting unique-parent structural theorem is **original-source Lean verified** in [manual CI 42541859868](https://github.com/FlareZ123/bb6/actions/runs/42541859868).

## Full inverse equations and admissibility

Use the unchanged [P1 source `T,G`](../agent1-p1-map/PosEvenForm.lean), [complete G ancestor theorem](../agent1-p1-map/GInverse.lean), [exact `inverseAt` equation](../agent1-p1-quarter/InverseIff.lean), and [`CountCone` constructor](../agent50-p1-l1-reset/ResetCount.lean). Each noninitial source counted inverse step from a parent `(b,d)` has
```text
b>=8, b%4=0, d%2=1, k>=2, c%2=1,
A = d+b/2+3 = 2^t*(c+3),
2*k+c+2*t+2=b+d,
child=(2*k-4,c+4).
```
Consequently, enumerate exactly `t=0,...,v2(A)-1` and put `Q=A/2^t`. Keep a step only if `Q>=4` (since `c=Q-3>=1`) and `b'=b+d-Q-2*t-3>=0` (equivalent to `k>=2`). Its child is precisely `(b',Q+1)`. Every such step decreases `b+d` by `2*(t+1)`. Record a terminal hit immediately if `Q+1=5`. Otherwise expand the child only when `b'>=8` and `b'%4=0`; a child failing these guards cannot be a parent of a further `CountCone` step. The right counter stays odd by construction.

The C++ reference scanner [stream_inverse.cpp](stream_inverse.cpp) uses `boost::multiprecision::cpp_int` for every machine counter and never truncates a huge `2^n`. The independent [inverse_python.py](inverse_python.py) directly computes `c,k` from the displayed source equations and keeps an active-state visited set. Both enumerators detected the same complete counts at the two historically capped cases.

## Why a visited set is unnecessary

**Stronger original-source Lean theorem:** [P1InverseNoMerge.lean](P1InverseNoMerge.lean) proves `unique_inverse_edge`: for *all* natural depths and valid `inverseAt` children, if the child counter pairs agree then **both parent counters and the inverse depth agree**, including the exceptional `c=1` right-five event. The proof uses the unchanged exact `inverseAt_sound`, `GAncestor_sound`, and `inverseAt_power` theorems. It passed [manual original-source CI 42542220876](https://github.com/FlareZ123/bb6/actions/runs/42542220876), ordinary axioms only. This gives a direct no-merging argument for every branch of the source-shaped inverse tree.

The original deterministic P1 counter transition additionally has the following exact two-step law whenever `k>=2,c>=3`:
```text
T (2*k-4,c+4) = some (2*k-1,c+2)
T (2*k-1,c+2) = some (G k c).
```
A source inverse edge has `G k c=(b,d)`; therefore any nonterminal inverse child with right counter at least 7 determines **exactly one** parent: apply the deterministic `T` twice. At a fixed parent and child, `c` is determined by the child's right counter and the factor `2^t` is determined by `A/(c+3)`; thus there cannot be repeated parallel edges. Combined with strict inverse mass decrease, the graph of expandable states rooted at the critical seed is a **tree**. Repeated states cannot occur on different inverse paths. The sole `c=1` exception has child right counter 5, which is the terminal event tested *before* pruning or expansion.

[Source-shaped Lean file](P1ActiveArborescence.lean) contains the two-step theorem; it compiled locally in Lean 4.36.0-rc2 against a minimal copy of the original `PosEvenForm` definitions, with ordinary foundational axioms. The identical short theorem also passed **manual CI 42541859868**, importing and compiling the **unchanged repository `PosEvenForm.lean`**. The theorem's printed axioms contain only Lean's standard foundation axioms; there are no `sorry` dependencies. The unique-parent argument above uses only the original deterministic definitions and source-complete ancestor equations.

## Reproducible exact computations

| Critical index | Expanded parent nodes | Enumerated legal outgoing edges | Dead-end children | Peak DFS stack | Right-five event |
| ---: | ---: | ---: | ---: | ---: | --- |
| 14 | 15 | 29 | 15 | 3 | absent |
| 286 | 155,987 | 311,973 | 155,987 | 366 | absent |
| **1614** | **1,735,095** | **3,470,189** | **1,735,095** | **1,471** | **absent** |
| **2622** | **799,283** | **1,598,565** | **799,283** | **582** | **absent** |

For the `q=164..1000` pass, **837/837** traversals finished with status COMPLETE under a cap of ten million expanded nodes per case: sum **7,799,899** expanded nodes, sum **15,598,961** legal outgoing edges, and maximum stack occupancy **1,254**. The largest tree was `q=633,n=10130`, with **3,343,447** expanded nodes and **6,686,893** edges. A local canonical tabulation with one row per q and columns `q,n,active,edges,inactive,peak` has SHA-256 `edce9fd3fbccb3609d4702604274adff11a6963c78d5d4f789de371c466e8b5c`; it can be regenerated from the scanner's q-range output. Only integer result fields contribute to the canonical table; elapsed seconds are excluded.

The reference C++ program accepts a lower/upper **n** range, a per-case active-node cap, and an optional `q` mode mapping a q range to `n=16q+2`. Compile with C++17 and Boost.Multiprecision; the scanned n values above are all even and at least 14. Every line reports `COMPLETE`, `CAPPED`, or `HIT`. Only `COMPLETE` plus no `HIT` is treated as an exhaustive negative result. The independent Python implementation reproduced the four listed n-index counts before the broad pass; its memory cost is larger because it intentionally stores all active states. Both implementations were corrected to require `c>=1` explicitly, then rerun; the counts were unchanged.

**Historical gap closed:** The previously one-million-state-capped cases `n=1614,2622` in Agent43's earlier report have now been fully traversed, with independent exact-integer reproduction. No additional implied conclusion about actual blank-root reachability follows from closure of these numerical cases.

## Mathematical frontier

The source [right-five reset-density theorem](../agent50-p1-subwall/README.md) requires `n<3*z+2*log2(n)+11` for a counted right-five endpoint at n>=14, with arbitrary cost and reset count, and [Agent43's two-shallow theorem](../agent43-p1-high-cost-reset-count/TwoRunWallExclusion.md) excludes all legal words `2^s(0|1)2^u(0|1)2^r` at the shifted wall. The finite streaming method offers much larger, independently reproducible fixed-index closures and a cheaper way to inspect candidate word automata. It does **not** bound `q` or close high-depth inverse paths uniformly.

A next decisive result would be a **parameter-uniform arithmetic/invariant proof** ruling out right-five for every admissible critical `n=16q+2`, or a genuinely legal positive right-five source witness. Even that would leave P1's other even exit and global BB(6) completeness obligations open.
