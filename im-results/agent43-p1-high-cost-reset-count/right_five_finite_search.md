# P1: exhaustive finite exceptional right-five inverse searches

**Current synthesis, 9 November 2026.** Exact integer traversal has found no right-five endpoint in the original source-shaped inverse `CountCone` from `(14*2^n-2*n-16,3)` throughout **all fixed n=14..1612**, **all n=1616..2620**, and now the previously incomplete **n=1614 and n=2622**. The later [Agent27 streaming search](../agent27-p1-finite/README.md) additionally exhaustively covered **all critical n=16q+2 for 164<=q<=1000**, building on the original report's q1..163 cases. The combined *finite* critical gateway range is now **q1..1000**, with no right-five endpoint found. The parameter-uniform statement remains **unproved**.

## Exact inverse semantics and certificates

The source arithmetic is `inverseAt_iff_power_mass` in [InverseIff.lean](../agent1-p1-quarter/InverseIff.lean): from parent `(b,d)` with `b>=8,b%4=0,d` odd, each edge chooses `t,k,c` with `k>=2,c` positive odd,
```
d + b/2 + 3 = 2^t * (c+3)
2*k + c + 2*t + 2 = b+d
child=(2*k-4,c+4).
```
Thus every inverse depth is enumerated by `0<=t<v2(d+b/2+3)` with the stated arithmetic and positivity checks. For any source `CountCone` path the mass `b+d+2*m` stays constant, and along a forward traversal of inverse edges `b+d` drops by `2*(t+1)`. The graph is finite at each n.

The initial implementation [right_five_finite_search.py](right_five_finite_search.py) uses a visited set on `(b,d)`, preventing duplicate exploration. The newer [source-shaped scanner](../agent27-p1-finite/stream_inverse.cpp) proves a stronger practical observation: every expandable inverse child has a deterministic unique parent under the original `T^2`; thus the entire expandable subgraph is a rooted tree, with no visited set necessary. Right-five children are checked *before* discarding unexpandable nodes. This reduces the space cost from millions of remembered states to the DFS stack and allows the previously capped trees to finish. An [independent Python implementation](../agent27-p1-finite/inverse_python.py) reproduced the previously unresolved counts from the explicit original `k,c` equations.

A complete negative search is an exact-integer calculation over all source-shaped branches for **that one fixed n**. It is neither a Lean proof quantified over all n nor evidence that the authentic blank-root forward orbit halts or does not halt.

## Completed computations

| n | Initially reported distinct states (including dead ends) | Later expandable states | Legal edges | Right-five |
| ---: | ---: | ---: | ---: | --- |
| 14 | 30 | 15 | 29 | absent |
| 18 | 102 | not separately tabulated | not separately tabulated | absent |
| 30 | 1,502 | not separately tabulated | not separately tabulated | absent |
| 78 | 334 | not separately tabulated | not separately tabulated | absent |
| 142 | 2,358 | not separately tabulated | not separately tabulated | absent |
| 286 | 311,974 | 155,987 | 311,973 | absent |
| 510 | 30 | not separately tabulated | not separately tabulated | absent |
| 1022 | 70 | not separately tabulated | not separately tabulated | absent |
| **1614** | previously capped at 1,000,000 | **1,735,095** | **3,470,189** | **absent, complete** |
| 2046 | 70 | not separately tabulated | not separately tabulated | absent |
| 2338 | 123,950 | not separately tabulated | not separately tabulated | absent |
| **2622** | previously capped at 1,000,000 | **799,283** | **1,598,565** | **absent, complete** |

The initial Python search completed every individual n=14..1612 and 1616..2620 without a right-five endpoint. Its peak full visited-state count was 311,974 (n286) in the first interval and 123,950 (n2338) in the second. Attempts to increase its one-million cap at n1614 had exhausted memory. The new memoryless method closes those two cases and extends the special critical family `n=16q+2` from q164 through q1000, **837 additional complete searches** with **7,799,899** total expandable states and **15,598,961** total inverse edges. The largest of these is n10130 (q633) with 3,343,447 expandable states; the peak DFS stack among all 837 is 1,254.

The original program and new reference implementation are preserved separately. See [the complete streaming dossier](../agent27-p1-finite/README.md) for the tree argument, independent reproduction, exact code, counts and scope.

## Consequences and open proof obligation

For the critical gateway `n=16q+2`, **all q1..1000** have source-shaped, finite, no-right-five results. With the original source dichotomy (`source_critical_either_gate_needs_near_resets`), these finite results would remove the right-five alternative for the specified first thousand q values, leaving the separate affine-wall/other even-exit proof obligation. The computations have **not** been lifted to a uniform Lean parametric certificate; their outputs are described as exact numerical results.

The crucial open problem is to exclude **every** n and every reset count, or find a source-consistent right-five witness, while separately deciding the other P1 gates. Larger bounded traversals can support conjectures and test attempted symbolic invariants. They cannot establish the BB(6) value by extrapolation.
