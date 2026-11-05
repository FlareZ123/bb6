# P1 dyadic shadow cone: complete finite-parameter census (Agent 9)

**Updated status 2026-11-05:** Original-source Lean now certifies bounded-cost source-to-shadow graph containment for all q and an unconditional odd-cone cost ceiling at q=29. Earlier dated sections record the prior computational stage. The global P1 halting problem remains open. No individual machine is asserted decided and no BB(6) bound is claimed. Source proof integration, including all authentic predecessor-exit cases, remains to be done.

This work closes the *computational node-cap gap* for the n=16q+2 P1 two-feeder inverse searches at q=498,633,774, and reproduces q=294. It compresses astronomical P1 counters to a two-integer graph. The original inverse rules, two-feeder geometry and preexisting universal 15q cost-to-power-gap theorem are due to Agents 1, 45 and 47. The new contribution is the projected graph, its parameter-specific safety certificates, complete search at previously capped indices and the source correspondence argument.

## Actual source context

Use q>=1, P=2^(16q), u=7P-4q-3. The original-source-certified [two-feeder theorem](../agent45-p1-deep-two/P1TwoSector.lean) gives the critical-target iff either rooted blank-reachability of

* L0=(4u-4,4u+9), with source mass S=56P-32q-19; or
* L1=(6u-2,2u+5), with source mass S=56P-32q-21.

The original [OddCone](../agent1-p1-quarter/OddConeMass.lean) tracks an exact source `inverseAt` chain with odd second counter and accumulated cost m. Source invariance: b+d+2m=S. At each odd hub (b,d), the true inverse has k_0=b/4-1, c_0=d+b/2, and iterates

```text
k_(t+1) = k_t + ((c_t-3)/2)/2 + 1
c_(t+1) = (c_t-3)/2
```

while c_t>=3 is odd. The depth-t output is (2k_t-4,c_t+4); an odd-output, b divisible by four branch increments m by t+1. This is copied algebraically from the existing `P1FiniteInverse` and `MassInverse` source, not an independent claim of source equivalence.

## Exact shadow transformation

Set N=16q, h=8 on L0 and h=9 on L1, and L=N+h. At root, set (m,z)=(0,12q+4) for L0 and (0,10q+4) for L1. Define E=L+m and w=E-z.

A true odd-hub node can be represented as

```text
b = A * P - 4*w
d = S - 2*m - b
0 < A < 56
alpha = 2^m * A,  a positive integer below 56*2^m
```

Initially A=28 on L0 and A=42 on L1, and w is 4q+4 or 6q+5 respectively. Source mass gives the exact identity

```text
s := d+b/2+3 = (56-A/2)*P - 2*z.
```

For z>0, write v=v2(z). Under the checkable safety condition m+v+3<=N, the first term in s is divisible by 2^(v+2), while 2z has exact valuation v+1. Thus **v2(s)=v+1**, meaning the true inverse outputs c_t odd precisely at depths 0<=t<=v; at t=v+1, c_t is even. The separate positive-size safety condition below guarantees c_t>=3 through that final depth.

For every odd-output inverse depth t<=v, a direct substitution of the source mass and inverse equations yields

```text
m' = m+t+1
z' = (L+m+t-1+z/2^t)/2
w' = (L+m+t+3-z/2^t)/2
A' = 56 - (56-A/2)/2^t
alpha' = alpha + 56*2^(m+1)*(2^t-1).
```

Since the P component is divisible by four, b' is divisible by four **if and only if** the displayed z' is an integer, equivalently L+m+t-1+z/2^t even. This gives a fully integer two-counter graph, with no need to store P or A:

```text
(m,z) --t--> (m+t+1, (L+m+t-1+z/2^t)/2)
    for 0<=t<=v2(z), if the numerator is even.
```

Algebraically 0<A'<56, and the displayed alpha' remains a positive integer with 0<alpha'<56*2^(m'). The source `OddCone` mass equation is preserved. All accepted abstract edges therefore have an exact candidate source lift. Rejected odd-output branches have left counter congruent to 2 modulo 4; handling those branches against authentic blank reachability uses the established source Reach parity restrictions, a separate theorem.

The elementary inductive safety invariant `z>0 and w=L+m-z>=4` holds at the root and on every accepted edge. At t=0, integrality forces odd w and w'=(w+3)/2>=4. For t>=1, z/2^t <= z-1 and the displayed formula gives w'>=4; positivity of z' follows from L>=24. Consequently z<=L+m-4.

## Finite safety conditions checked by the program

For each full abstract graph, let M be maximum m, V maximum v2(z), and T maximum even-output inverse cost m+v2(z)+2. The code checks

```text
M+V+3 <= N
2^(N-M) >= 4*(L+M)+16
28*2^N > 2*(L+M) + 12*2^V
T <= 15*q
edge_count = node_count-1.
```

The second inequality ensures that every represented odd hub and valid predecessor has b>=16; with source mass it also ensures d positive, and d is odd. The third ensures all `inverseAt` counters c_t are at least three even at the last even-output depth. The first certifies the 2-adic valuation equality at every abstract node. The graph-tree equality rules out merged abstract paths, so the rational coefficient A is uniquely lifted from each root; no hidden multiplicity of source states is being discarded. These explicit checks are stronger than a mere finite-time simulation.

The final check T<=15q permits use of Agent 1's already source-proved [medium_root_even_not_reachable](../agent1-p1-quarter/MediumConeReach.lean) to reject *any genuinely blank-reachable even-second-counter inverse terminal* from an original odd cone. The source `Reach` exclusion for other exits and an original-source Lean bridge are still required before declaring the corresponding three individual critical indices formally impossible.

## Reproducible census

[shadow_census.py](./shadow_census.py) performs exact integer graph exhaustion with no node-count or recursion-depth cap. All 2,996 feeder graphs for q=3..1500 satisfy every safety assertion. For q=1,2, the code instead directly iterates the original full-size b,d inverse recurrence because the coarse global safety inequality is unnecessarily strong. In total, **3,000 feeder graphs / 8,637,712 recorded nodes** are exhausted, including 8,637,516 shadow nodes for q>=3.

| q | critical n=16q+2 | L0 projected nodes | L1 projected nodes | L0 max even cost | L1 max even cost |
|---:|---:|---:|---:|---:|---:|
| 294 | 4706 | 161,223 | 160,455 | 2,517 | 2,516 |
| 498 | 7970 | 1,190,152 | 1,189,594 | 3,501 | 3,500 |
| 633 | 10130 | 1,671,923 | 1,671,523 | 4,965 | 4,964 |
| 774 | 12386 | 308,674 | 309,452 | 2,093 | 2,092 |

q=294 had previously been exhaustively computed by Agents 9 and 45. **q=498,633,774 were previously capped**, so their full projected enumeration is the new computational coverage. The maximal risks M+V+3 across those roots are respectively at most 3,515, 4,979 and 2,106, far below N=7,968, 10,128 and 12,384. The longest true even-branch cost is also well below 15q. Each shadow graph has exactly nodes-1 edges, giving a rooted tree in every checked case.

Independent source-equivalent direct `(b,d,k,c)` inverse enumeration, with mass and exact dyadic-coefficient assertions, agreed node counts and maximal even costs at both roots for q=38,101,294. The direct routine is included in the script; q=1,2 also run directly. Recompute the complete published census by executing `shadow_census.py` with Python 3, without command-line arguments. Pass a subset of q values as optional arguments to restrict the verification.

## Standalone Lean kernel verification

[ShadowAlgebra.lean](./ShadowAlgebra.lean) has been locally compiled with the supplied **Lean 4.36.0-rc2** toolchain (commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`). Its theorem `polynomial_step` proves the full, all-integer coefficient transport identity from seven explicit mass/inverse/quotient equations. `shadow_step_preserves_offset` proves the unconditional four-unit margin for every positive dyadic quotient and parity-correct next shadow state. `valuation_witness` proves exact cancellation and parity of the low-order 2-adic term for all natural exponents. The `#print axioms` output for each states only combinations of `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`. The module imports Lean itself and does not import the original source machine, so this is arithmetic kernel verification, with that precise provenance boundary.

## Scope and immediate follow-up

The recurrence and coefficient induction are a mathematical proof sketch checked against exact source-equivalent arithmetic and exhaustive finite code. **They have not yet been formalized in Lean against the unchanged original P1 `inverseAt` and `Reach` definitions.** The Python assertions establish the stated outputs only under the correctness of this independent implementation and its correspondence derivation. These certificates should therefore stay in `im-results/`, not the academic `results/` catalogue.

The most useful follow-up is to kernel-check a general shadow abstraction simulation theorem against `P1FiniteInverse`, plus a finite-graph inductive closure certificate for q=498,633,774. Then combine the original source's complete odd/left-mod4/small-source inverse cases, its `medium_root_even_not_reachable` theorem and the two-feeder iff into certified `¬Reach` statements for critical n=7970,10130,12386. This would be finite genuine blank-root exclusions, still far from a uniform P1 nonhalting proof or BB(6).


## New source-level Lean certification (2026-11-05)

The earlier source-correspondence and finite-certification gaps are now partly discharged. The original-source [manual Lean CI 42040254226](https://github.com/FlareZ123/bb6/actions/runs/42040254226) proved:
- `source_odd_iff_offset_dvd`: a genuine `inverseAt` odd output occurs precisely at depths with `2^t∣z` for a safely encoded hub;
- `source_odd_child_iff_integral`: the original next left counter is divisible by four precisely when the compressed numerator is even;
- `original_odd_shadow_step`: the complete exact natural-number coefficient and offset update at each authentic source odd edge;
- `bounded_l0_cone_in_shadow_graph`, `bounded_l1_cone_in_shadow_graph`: every original `OddCone` node with left counter divisible by four and accumulated cost `m+2≤16q` is in the exact two-integer `ShadowReach` graph of the earlier computational census, for either original critical feeder root.

The proof source and dependency chain is in `ShadowDepthArithmetic.lean`, `ShadowDepthSource.lean`, `ShadowSourceTransport.lean`, `ShadowParityArithmetic.lean`, `ShadowParitySource.lean`, `ShadowCast.lean`, `ShadowSourceStep.lean`, `ShadowConeLift.lean`, `ShadowFeederRoots.lean`, `ShadowGraphBridge.lean`, and `ShadowGraphFeeders.lean`. Every claimed theorem imports unmodified original `inverseAt`, `OddCone`, and the original G map through established source lemmas. Kernel axiom reports contain only standard axioms.

An independently kernel-checked special case at `q=29` was verified in [manual CI 42042463934](https://github.com/FlareZ123/bb6/actions/runs/42042463934). `ShadowQ29Finite.lean` proves exact inductive graph closure at L0 (12 nodes) and L1 (14 nodes), both with maximum odd inverse cost m=10, and `ShadowQ29Graph.lean` connects these closed graphs to the original bounded-cost source cones. Thus `m+2≤464` implies `m≤10` for any authentic left-divisible-by-four odd-inverse node at these roots.

A further modular lemma observes that none of these 26 listed shadow nodes has z divisible by 256. If an authentic inverse input depth were at least 9, the original source's exact binary power equation and the shadow mass identity force `256∣z`, contradicting the finite invariant. This is formalized in `ShadowQ29No256.lean`, `ShadowQ29DepthArithmetic.lean`, and `ShadowQ29DepthSource.lean`. The full-cone induction without any prior cost cutoff in `ShadowFiniteInvariant.lean` and `ShadowQ29FullCone.lean` **passed original-source Lean 4.36.0-rc2 CI [42043587196](https://github.com/FlareZ123/bb6/actions/runs/42043587196)**. The new final theorems `q29_l0_full_authentic_cost` and `q29_l1_full_authentic_cost` prove m≤10 for every authentic q29 L0/L1 `OddCone` state with b divisible by four, without any prior cost assumption. The only axioms are the standard Lean axioms, with no `sorryAx`.

The source-to-shadow theorem certifies forward containment of authentic *odd* inverse paths. A P1 halting exclusion still needs to handle every authentic non-odd terminal source including even-right exits, exceptional c=1 and other special cases. The finite q29 graph and large q498/633/774 graphs are not a universal BB(6) bound. All these intermediate certificates remain in `im-results/`.
