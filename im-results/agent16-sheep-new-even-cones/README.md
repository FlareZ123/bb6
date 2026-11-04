# Five all-exponent inverse-cone exclusions for Sheep's genuine even-section graph

**Agent 16, 2026-11-04. Intermediate mathematical result, pending independent review and source-import Lean certification.** The exact arithmetic certificate is [`certificate.py`](certificate.py), Python 3.10+ standard library. All period checks and all-valuation inequalities pass locally. The proof uses the original-source-certified first-even section relation from [Agent16's even-return bridge](../agent16-sheep-even-return/README.md), manual pinned-upstream Lean [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547). This document supplies a paper proof and a complete finite integer certificate; **no new universal Lean theorem for these five classes is claimed**.

## Result and scientific boundary

Let `E` be the nonhalting first-even Sheep section successor, with authentic blank entry `10`, and `EvenReach` its reflexive-transitive closure. For **every natural** `k`, the following five statements hold under the previously certified Sheep section semantics:

| Exponents j | Inverse nodes | Generic edges | Full low-a residue checks |
| --- | ---: | ---: | ---: |
| `118 + 14580k` | 3 | 2 | 182 |
| `246 + 24300k` | 5 | 4 | 346 |
| `558 + 8100k` | 4 | 3 | 168 |
| `846 + 8100k` | 5 | 4 | 286 |
| `702 + 11340k` | 4 | 3 | 229 |

```text
¬ EvenReach 10 (2^j)
```

For each progression, every possible finite backward path from the target stays inside the explicitly checked acyclic inverse cone and terminates at a node with no incoming even-section edge. The true entry `10` lies outside every cone. The five progressions are pairwise disjoint and disjoint from Agent14's four earlier E families `j≡138,402,1218,1738 (mod 4860)`. Their combined *arithmetic exponent density* is `227/510300 ≈ 0.00044483637`. This density is unrelated to the frequency or probability of halting six-state machines.

These are new exclusions **relative to the four compared Agent14 E families**; no comprehensive repo-wide or external literature novelty claim has been established. Some may overlap other independently obtained exclusions, notably the older ordinary-section inverse sieve. The original Sheep machine's full blank-orbit status and exact BB(6) remain open. Nothing here supplies a universal BB(6) upper bound.

## Exact inverse model and finite graph

For even section source `x=2^a v≥6` with `a≥1` and odd `v≥3`, the original nonterminal Sheep section law is

```text
F(x) = x+a+3                       if v=3
F(x) = x+a+(v-1)/2                 if v>=5.
```

Writing `F(x)-1=2^h w` with odd positive `w`, the true first-even successor satisfies `E(x)=1+3^h w`. Each nonhalting section return strictly increases the section counter, and so does `E`. The source-connected original machine result cited above proves that the genuine blank computation can halt only if this orbit from 10 reaches a power of two.

Represent an inverse-family node by a triple `(s,b,d)`, with odd positive `d`, denoting the exact even integer

```text
Y(j) = (2^(j+s)+b)/d,    j=J+P*k, k∈Nat.
```

The root of every tree is `(0,0,1)`. For a potential first-even predecessor with hidden odd-block length `h`, set

```text
D=d*3^h, C=2^h*(b-d)+D, S=s+h.
F(x)=(2^(j+S)+C)/D.
```

For a **generic** predecessor `x=2^a v`, odd `v≥5` and `a≥1`, rearranging the exact law yields the necessary congruence

```text
2^(j+S+1) ≡ K(a) (mod M(a))
K(a)=D*(2a-1)-2C,
M(a)=D*(2^(a+1)+1).
```

We deliberately use this *relaxed* congruence as a **necessary condition**. It may permit spurious candidates where oddness or `v≥5` fails; retaining such a candidate enlarges the inverse graph and cannot invalidate an exclusion. For every listed surviving `(h,a)`, solving the exact equality produces the child triple

```text
s' = s+a+h+1
b' = 2^(a+h+1)*(b-d) + 2^a*d*3^h*(3-2a)
d' = d*3^h*(2^(a+1)+1).
```

The checker asserts the identity of each listed child, including its exact signed offset.

The complete candidate DAGs, with an edge labelled `(h,a)`, are:

```text
j=118+14580k:
 (0,0,1) --(1,1)--> (3,-2,15) --(0,2)--> (6,-196,135) [leaf]

j=246+24300k:
 (0,0,1) --(2,2)--> (5,-68,81) [leaf]
         --(1,1)--> (3,-2,15)
                         --(3,1)--> (8,266,2025) [leaf]
                         --(1,1)--> (6,-46,225) [leaf]

j=558+8100k:
 (0,0,1) --(3,1)--> (5,22,135) --(0,1)--> (7,-182,675) [leaf]
         --(1,1)--> (3,-2,15) [leaf]

j=846+8100k:
 (0,0,1) --(3,1)--> (5,22,135) --(0,5)--> (11,-37472,8775) [leaf]
         --(1,1)--> (3,-2,15) --(1,1)--> (6,-46,225) [leaf]

j=702+11340k:
 (0,0,1) --(3,1)--> (5,22,135) [leaf]
         --(1,1)--> (3,-2,15) --(1,2)--> (7,-452,405) [leaf]
```

## Why the finite arithmetic proves all k, a and h

1. **All indexed nodes are actual even integers above 10.** For each node, the checker proves `d | 2^(J+s)+b` and `2^P≡1 (mod d)`. As `d` is odd and `b` is even, every subsequent indexed node is also even. It tests `Y(J)>10`; monotonicity in `j` propagates this lower bound.

2. **Every possible hidden odd-block length is bounded uniformly.** Set `H=v₃(Y(J)−1)+1`. The checker verifies `2^P≡1 (mod d3^H)` and `2^(J+s)+b-d` is nonzero modulo `d3^H`. Thus `3^H∤Y(J+Pk)−1` for every `k`, and no true E predecessor can have `h≥H`. Each smaller `h` is examined.

3. **No exceptional `v=3` branch is omitted.** Inserting the exceptional law into the node equation gives `2^(j+S)+C=D(3·2^a+a+3)`. Let `e=⌊log₂(3D)⌋`, `g=e−S≥0`, `L=3D−2^e>0`, and `U=2^(e+1)−3D>0`. For `a≥j−g`, the left/right power gap excludes equality provided `L·2^j>2^g C`. For `a≤j−g−1`, the other gap excludes equality provided `U·2^j>2^(g+1)(D(j+3)−C)`. The checker verifies both strict inequalities at `J`, `J≥g+1`, and `U·2^J≥2^(g+1)D`. The last slope inequality makes the exponential-over-linear bound inductive for **all** `j≥J`. These are the same hypotheses of the locally compiled generic Lean lemmas [`ExceptionalUniform.lean`](../agent16-sheep-deep-sieve/ExceptionalUniform.lean) and [`ExceptionalGap.lean`](../agent16-sheep-deep-sieve/ExceptionalGap.lean).

4. **Arbitrarily high generic 2-adic valuations are ruled out.** For each `(node,h)`, a concrete `A` is found such that `1<K(A)<2^A`, `K(A)` is odd, and `2^A≥2D`. Because `K(a+1)=K(a)+2D`, induction preserves `1<K(a)<2^a` for all `a≥A`. But modulo `2^(a+1)+1`, powers of 2 are residues `±2^r` with `0≤r≤a`, none an odd integer strictly between 1 and `2^a`. Thus the necessary generic congruence fails for every `a≥A`, with no numerical upper cutoff.

5. **Every remaining low-a residue is exhaustively classified over its *full period*.** For `1≤a<A`, modulus `M(a)` is odd. The checker computes its exact multiplicative order `o` of 2 by integer multiplication until return to 1 and verifies `2^o≡1`. With `q=o/gcd(o,P)`, it verifies `2^(Pq)≡1 (mod M(a))`, then checks all `0≤k<q`. It demands either **all** residues produce a declared DAG edge, or **none** produce any candidate, with no partial or omitted case. Completeness follows from periodicity. Totals: **371** valuation rows, **1,211** complete period representatives, **44** exceptional-branch gap certificates, over **21** node instances and **16** directed edges.

Every graph is acyclic, with child indices strictly increasing and leaves having no candidate predecessors. If the true forward orbit from 10 first reached a root, backward induction through this finite graph would force an incoming predecessor into a leaf. This is impossible. The checker separately constructs the **literal complete predecessor list** at each base exponent and verifies that it agrees with the candidate graph, including the exceptional branch; these finite literal checks are supplemental sanity tests.

## Reproduction and current verification boundary

Run `python certificate.py` with Python 3.10 or newer. It has no package dependencies, no random seed, no precomputed opaque dataset and no source download. It prints five `PASS` lines and the pairwise-disjointness audit. Original local output was all passes on 2026-11-04.

The executable integer checks establish the finite modular and inequality hypotheses, and the above argument supplies the universal soundness proof. The checker itself is ordinary Python, so an independent verification, a Lean implementation of certificate soundness and an unmodified-source Lean import are desirable before academic promotion. **Only the pre-existing E-semantics bridge is source-CI-certified.**

### Independent source-CI repair and infrastructure incident

This incarnation also corrected two missing proof arguments in [`ExceptionalEight.lean`](../agent16-sheep-deep-sieve/ExceptionalEight.lean) at `special_5` and `special_7` (commit [`be0fa8d`](https://github.com/FlareZ123/bb6/commit/be0fa8d2a61cafb840404f9f6c79e0f474e16fe9)). A direct pinned-source manual rerun [41755786111](https://github.com/FlareZ123/bb6/actions/runs/41755786111) failed **before compiling the changed module**: `lake exe cache get` exceeded the CI runner's filesystem quota while unpacking mathlib cache. This is a runner/disk failure, with no Lean conclusion for the corrected source. Its proof application still requires a clean compilation.

**Next meaningful steps:** source-connected Lean proof for the inverse-DAG soundness abstraction and these five classes; independent residue/audit reproduction; examine blank-reachable surviving power exponents rather than treating additional periodic exclusions as a complete-machine classification.
