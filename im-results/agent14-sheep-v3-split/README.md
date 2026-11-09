# Uniform 3-adic inverse sieve for Sheep's power-of-two halting gates

**Agent 14, 9 November 2026.** **Research status:** all-integer, all-exponent mathematical proof with a reproducible complete-period certificate derived from Sheep's original-source first-even transition equations. The entire new theorem has not been assembled as a single pinned-original-source Lean proof. These exclusions remain intermediate `im-results/` research pending independent review and external-priority comparison. No full Sheep blank-start decision or exact BB(6) value follows.

## Main theorem and quantitative advance

Let `E` be the authentic even-first-return relation of the six-state Sheep Turing machine `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` and `EvenReach` its reflexive-transitive closure. The original blank-start machine enters this section at state value **10**. Its halting condition is the eventual encounter of an even power of two.

For `0 ≤ s ≤ 16`, fix `r` with `1≤r≤63` and `3∤r`, and consider every integer `k≥0`. Define

```
n = 3^s * (r + 63*k),    j = 17496*n,    target = 2^j.
```

The [complete-period certificate](./stratum_certificate.py) finds a set `R_s` of residues `r` with **no incoming authentic even-return edge** into `target` for every `k`. The [five-phase refinement](./phase_refine.py) additionally excludes phases of otherwise surviving rows. A new [finite inverse-chain certificate](./inverse_chain.py) follows every exact source branch for several of the remaining powers, discharging four whole further progressions and five selected nine-phase progressions. Each excluded power satisfies `¬ EvenReach 10 (2^j)` at every time.

| Valuation s | Unsplit closed r /42 | Phase-refined closed (r,t) /210 |
| ---: | ---: | ---: |
| 0 | 30 | 150 |
| 1 | 30 | 150 |
| 2 | 12 | 132 |
| 3 | 30 | 150 |
| 4 | 30 | 150 |
| 5 | 30 | 150 |
| 6 | 12 | 132 |
| 7 | 12 | 132 |
| 8 | 30 | 150 |
| 9 | 12 | 132 |
| 10 | 25 | 125 |
| 11 | 25 | 125 |
| 12 | 10 | 110 |
| 13 | 20 | 100 |
| 14 | 20 | 100 |
| 15 | 20 | 100 |
| 16 | 8 | 88 |

The certified progressions are disjoint: each has an exact 3-adic valuation `v3(n)=s`, a distinct coprime residue `r` modulo 63, and, when refined, a distinct phase `t` modulo 5 in `k=t+5m`. The **combined rigorous lower natural-density bound** among positive integer indices `n` in `j=17496*n` is

```
17-stratum five-phase predecessor-free density:
    9597932614/13559717115
Extra finite inverse-chain closures at s=0:
    4/63 + 25/(9*63) = 61/567
Combined:
    11056738159/13559717115 = 81.54106804167%.
```

The original unsplit single-root sieve gives `1849545554/2711943423 = 68.20000514443%`; its complete five-phase refinement gives `70.78269061663%`. The deeper inverse-chain theorem supplies another `10.758377425%` of disjoint progressions. This is a density of predecessor-free **exponent indices in this sparse subsequence**. It is not an estimate of the probability that the original machine halts. The unclassified high-valuation tail `v3(n)≥17` has natural density `3^(-17)≈7.74e-9`; classes left open within the first 17 strata can still have large unknown inverse cones. The result gives a rigorous **lower bound** on predecessor-free density; it does not establish the full exact density.

Previously, the [222-family certificate](../agent14-sheep-inverse-dag-222/README.md) intentionally omitted the seven exponent residues `j=17496m (mod 122472)` because their hidden 3-adic predecessor valuation was unbounded in that unsplit progression. Splitting by `v3(n)=s` now certifies infinitely many progressions within precisely this formerly excluded sector. These new progressions do not overlap the original 222 classes.

## Mathematical mechanism

### Exact hidden 3-adic valuation

`17496=8*3^7`. Writing `n=3^s(r+63k)` with `3∤r`, the standard lifting-the-exponent identity proves

```
v3(2^(17496*n)-1)
= v3(2^2-1)+v3(17496*n/2)
= 8+s.
```

An even-return target has the exact form `y=1+3^h*u` with positive odd `u`. Consequently every possible incoming even-return edge has `0≤h≤8+s`. This bound holds uniformly for every `k` inside each stratum.

### Exhaustive generic inverse cases

The original-source inverse splitter [`SheepEvenSourceAlgebra.original_even_edge_inverse_cases`](../agent14-sheep-even-inverse/SheepEvenSourceAlgebra.lean) covers any genuine even incoming source `x=2^a*v`, with `a≥1` and odd `v≥5`, by the equation

```
3^h*(2^(a+1)+1)*v + 2*a*3^h + 2^(h+1)
 = 2^(j+h+1) + 3^(h+1).
```

Put `D=3^h`, `M=D*(2^(a+1)+1)`, and `K(a)=D*(2*a-3)+2^(h+1)`. Thus every generic source necessarily has

```
2^(j+h+1) ≡ K(a) (mod M).
```

For each fixed `h`, find a finite `A_h` such that `1<K(A_h)<2^A_h` and `2^A_h≥2D`. This interval persists for all `a≥A_h` because `K(a+1)=K(a)+2D`; `K(a)` is odd. The source-independent, already Lean-kernel-proved [signed odd-remainder gap theorem](../agent14-sheep-even-inverse/SheepOddGap.lean) rules out a power of two congruent to such a `K(a)` modulo `2^(a+1)+1`. That modulus divides `M`, so **all generic a≥A_h are impossible**.

For each remaining pair `0≤h≤8+s`, `1≤a<A_h`, the certificate calculates an exact integer `q>0` such that

```
2^(17496*63*3^s*q) ≡ 1 (mod M).
```

It tests **every phase** `k=0,1,...,q-1` of the necessary congruence. Therefore the row is excluded for **all nonnegative k**, without a guessed cutoff. The largest checked period is `q=43`. For a certified `r`, every generic row fails all its phases. Rows can have negative integer `K(a)`; Python's modular remainder correctly computes the integer congruence.

The finite modular calculation is a proof certificate: each small modular multiplication, modulus and period is explicitly checked by reproducible source. In every stratum, each remaining candidate pair has complete phase period `q=1` or `q=5` with respect to the `k` parameter. This is checked after the *entire* inverse census, including exclusions of all other `q` values. The five-phase refinement therefore checks all `t=0..4` for each `r`, and certifies the empty-predecessor phases for every `k=t+5m`. The complete refined period is `315*3^s` in `n`, while the maximum period needed for any intermediate row remains `43`. It is not yet a Lean-kernel result for the entire 17-stratum union.

### Exceptional odd-cofactor-three sources

The original-source alternative for `v=3` is

```
3^h*(3*2^a+a+2)+2^h = 2^(j+h).
```

For `h≤24` and `a≥100`, the exact base inequalities `0<R(100)<2^100` and `3^h<2^100`, with `R(a)=3^h*(a+2)+2^h`, propagate by induction to `0<R(a)<2^a`. The left side lies strictly inside

```
(3^(h+1)*2^a, (3^(h+1)+1)*2^a).
```

This interval contains no power of two, since the integer `3^(h+1)` is not a power of two and its next power-of-two integer is at least `3^(h+1)+1`.

For `a<100` and `h≤24`, exact inequalities prove the left side is smaller than `2^140`, while `2^(j+h)≥2^17496`. Therefore the exceptional branch is impossible throughout the 17 strata.

Finally every reachability path from the genuine seed 10 to a target `2^j>10` has a last edge. Since all possibilities for this last edge were excluded, the target is unreachable at every time.

## Special simplicity at s=0

The first stratum, `3∤n`, has only 87 low generic rows with periods at most 17. The sole possible congruence-surviving source valuations are `(h,a)=(3,6)` when `n≡1 (mod7)`, and `(8,2)` when `n≡8 (mod9)`. The other **30 residues modulo 63** are predecessor-free:

```
2,4,5,7,10,11,13,14,16,19,20,23,25,28,31,
32,34,37,38,40,41,46,47,49,52,55,56,58,59,61
```

The separate [`certificate.py`](./certificate.py) prints and verifies this small special case. The general [`stratum_certificate.py`](./stratum_certificate.py) contains all 17 strata, including the original 30.

## Deeper finite inverse-chain closure at s=0

The first-level necessary inverse congruence leaves only two root edge labels: `(h,a)=(3,6)`, forcing source node

```
Z = (2^(j+10)-16576)/3483,
```

and `(h,a)=(8,2)`, forcing

```
X = (2^(j+11)-28292)/59049.
```

These affine identities follow exactly from the original source splitter. Every genuine ancestor along the respective edge must equal the displayed integer value. The reusable h=0,a=2 inverse identity is `parent(y)=(8*y-12)/9`. Its two applications to Z produce the exact chain

```
root 2^j <- Z <- T <- U
T = (2^(j+13)-174404)/31347
U = (2^(j+16)-1771396)/282123.
```

For `j=17496*(r+63*k)` and each `r` in `{1,8,22,43,50}`, the exact 3-adic checks force the hidden inverse valuation into each of Z, T and U to be **h=0 for every k**. Complete-period modular sieves prove that Z and T have only `a=2` as a possible generic even source. They prove U has **no even source at all**, after excluding high-`a` and exceptional branches by the universal gap. Thus the entire root Z branch is excluded for every k in those five classes.

Four classes `r∈{1,22,43,50}` have no alternative root branch and are therefore blank-even unreachable for all k. The class `r=8` also admits root branch X and must be treated separately.

For `r∈{8,17,35,44,62}`, subdivide `k=t+9m`. The [inverse-chain script](./inverse_chain.py) proves that precisely these five phases for each r force hidden h=0 into X and exhaust all possible generic/exceptional sources:

```
r=8:  t in {0,1,3,4,7}
r=17: t in {0,3,5,6,8}
r=35: t in {0,1,4,6,7}
r=44: t in {0,2,3,5,6}
r=62: t in {1,3,4,6,7}
```

The condition h=0 is maintained throughout each phase progression because `2^(17496*63*9)≡1 mod3^11`; each remaining generic `a` is checked for a complete multiplicative period. In these selected phases X has **no incoming even edge**. The Z branch for r8 was already closed by the finite chain, so all 25 listed `(r,t)` progressions give unconditional root exclusions.

The four full r-progressions contribute `4/63` to the density among n. The 25 classes with period `9*63` contribute `25/(9*63)`, disjoint from the prior 17-stratum first-level certificate. The remaining r=29 Z corridor and r=26,53 higher-3-adic X branches are **open**. This distinction avoids misclassifying synthetic affine ancestors as actual blank-root reachability.

All finite generic low-a checks use the *exact* original inverse equation and complete modulo periods. The script also checks every requisite h=0 valuation at a modulus high enough for each affine denominator and verifies the high-a/exceptional bounds. A formal Lean import of these new chain assertions remains pending.

## Reproduction and open obligation

Run `python stratum_certificate.py`, `python phase_refine.py`, and `python inverse_chain.py` (Python 3.10+), requiring only the standard library. The first script checks the complete modular orders, exceptional inequalities, row thresholds and the coarser rational density; the second imports that full census and strengthens the bound by certifying every `k mod 5` phase. The unsplit 17-element count vector is

```
[30,30,12,30,30,30,12,12,30,12,25,25,10,20,20,20,8].
```

The refined 17-element count vector, each entry out of 210 possibilities, is `[150,150,132,150,150,150,132,132,150,132,125,125,110,100,100,100,88]`. The five-phase rational density is checked against a fixed fraction in `phase_refine.py`, and the independent-chain new 61/567 contribution is obtained from four full residue classes and 25 nine-phase classes.

The necessary remaining task for fully source-integrated formal certification is an original-machine Lean theorem incorporating the LTE bound, all complete modular finite residue checks, the existing high-`a` odd gap and the exceptional-source exclusion. The [pinned original-machine Sheep bridge](../agent16-sheep-even-return/README.md) and [even-edge inverse splitter](../agent14-sheep-even-inverse/SheepEvenSourceAlgebra.lean) already exist. Separately, a global invariant resolving genuine reachability of **all** powers from the blank seed is still needed to decide this machine and ultimately BB(6).

The independently attempted unrelated 31104 three-node inverse-chain source workflow failed before compilation because its Lean toolchain download received HTTP 504; it is not evidence for or against these new claims. The unmodified arithmetic certificates passed locally in Python.
