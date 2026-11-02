# Six deepest new Sheep exclusions: an eight-node all-time inverse proof

**2026-11-02, Agent16. Intermediate arithmetic certificate.** This is an independently reproducible refinement of the depth-five extension in [README.md](./README.md). It isolates precisely the six classes which become excluded at depth **five**, using an eight-node directed acyclic inverse tree and a dependency-free Python checker [`verify_six.py`](./verify_six.py). The all-time mathematical inference is explained here. These six classes are part of the 52 new classes reported in the main certificate. They have no separate Lean-kernel closure proof yet.

## Claim

For the genuine Sheep blank-tape section, initially `t=5`, no finite sequence of defined return steps reaches a power `2^j` with

```text
j ≡ 426, 2046, or 2586 (mod 2700).
```

This comprises six exponent classes modulo 5400. The least possible `j` is 426, so all checks below may use the common lower bound `j≥426`.

## Eight exact inverse families

Write a symbolic family as `d*y=2^(j+s)+b`, where `d` is positive odd, `s` nonnegative, and `b` is a signed integer. The generic return equation `y=2^a*u+a+(u−1)/2` implies the necessary congruence

```text
2^(j+s+1) ≡ d*(2*a−1)−2*b     (mod d*(2^(a+1)+1)).
```

If a valuation `a` survives this congruence, its exact symbolic predecessor is another family:

```text
(s,b,d) -> (s+a+1, 2^(a+1)*b + 2^a*d*(1−2*a), d*(2^(a+1)+1)).
```

The checker directly rederives and asserts every surviving family transition. The exhaustive inverse DAG for each of the three residue progressions is:

<escape>
family 0: (0,0,1)      -> valuation 0 -> family 1
family 1: (1,1,3)      -> valuation 0 -> family 2
                       -> valuation 1 -> family 3
family 2: (2,5,9)      -> no generic parent
family 3: (3,-2,15)    -> valuation 0 -> family 4
family 4: (4,11,45)    -> valuation 0 -> family 5
                       -> valuation 1 -> family 6
family 5: (5,67,135)   -> no generic parent
family 6: (6,-46,225)  -> valuation 0 -> family 7
family 7: (7,133,675)  -> no generic parent
</escape>

The deepest root-to-leaf route has five inverse edges. Every listed node has symbolic value strictly greater than `5` for `j≥426`, so the initial section cannot itself be an ancestor leaf.

## Proving the generic branch exhaustive

For each family, set `K(a)=d*(2*a−1)−2*b`. The table gives an all-valuation cutoff `A`:

| Family | (s,b,d) | a below A | Admissible a |
|---|---|---:|---|
| 0 | (0,0,1) | 2 | 0 |
| 1 | (1,1,3) | 5 | 0, 1 |
| 2 | (2,5,9) | 7 | none |
| 3 | (3,-2,15) | 8 | 0 |
| 4 | (4,11,45) | 10 | 0, 1 |
| 5 | (5,67,135) | 12 | none |
| 6 | (6,-46,225) | 13 | 0 |
| 7 | (7,133,675) | 15 | none |

For every row the checker asserts `1<K(A)<2^A`, `K(A)` is odd, and `2^A≥2*d`. Since `K(a+1)=K(a)+2*d`, the strict odd gap `1<K(a)<2^a` persists at every `a≥A`. But for `M_a=2^(a+1)+1`, the complete residues `2^e mod M_a` are exactly `1`, powers `2^r`, and complements `M_a−2^r` for `0≤r≤a). None is an odd integer strictly between 1 and `2^a`. Therefore no generic parent with `a≥A` exists, uniformly for all exponents. This is the residue-gap theorem independently formalized in `im-results/agent40-sheep-third-preimages/ResidueGap.lean`.

For each `a<A`, the certificate provides a checked complete period `q` for the exponent index:

```text
2^(2700*q) mod [d*(2^(a+1)+1)] == 1.
```

Any exponent `j=r+2700*k` has the same residue as one of the **q** explicitly tested `k` values. The checker asserts exact modular equality for every `0≤k<q` against the predicted candidate set, for each of the three residues `r=426,2046,2586`. These are **72** independently verified periods and **195** excluded valuation-residue pairs. The largest listed period is 13, enabling fast reproducibility without symbolic algebra packages.

## The exceptional u=3 branch

At each family, let `h=floor(log2(3*d))−s`, so `2^(s+h)<3*d<2^(s+h+1)`, with positive gaps

```text
L=3*d−2^(s+h),   U=2^(s+h+1)−3*d.
```

For any special predecessor `y=3*2^a+a+3`, exact equality would force `2^(j+s)+b=d*(3*2^a+a+3)`. If `a≥j−h`, then `3*d*2^a ≥2^(j+s)+L*2^(j−h)`, and the special expression is too large whenever `L*2^j>2^h*b`. If `a≤j−h−1`, then `3*d*2^a≤2^(j+s)−U*2^(j−h−1)`, and the special expression is too small whenever `U*2^j>2^(h+1)*(d*(j+3)−b)`.

The certificate checks at `j=426` the first two strict bounds and also `U*2^426>2^(h+1)*d`. The third inequality ensures the exponential-over-linear second bound persists on every subsequent integer exponent by elementary induction. The first bound persists because `L>0`. Thus the exceptional case is absent for every `j≥426`, independently of whether `j` is in one of the progressions.

## Final inverse induction and reproducibility

Each node is strictly above initial section `5`; any first reachability proof would have a preceding return edge. For a generic predecessor the congruence and checked tail bound force one of the explicitly displayed children. The exceptional branch has no predecessor. Three leaves have no children; every other allowed edge descends to one of those leaves within five levels. Reverse induction establishes no first arrival and therefore excludes all six residue classes, uniformly in `j`.

The independent checker uses only Python 3 standard-library integers and makes no appeal to a bounded sample of exponents. It is simpler to audit than the original whole-5400 symbolic engine but intentionally covers only the six most deeply derived classes. The checker validates the finite arithmetic premises; the soundness theorem connecting these premises to unreachability is articulated above rather than checked in Lean. The fully original-machine source bridge exists independently in Agent22's verified module. The Sheep holdout and BB(6) remain open.
