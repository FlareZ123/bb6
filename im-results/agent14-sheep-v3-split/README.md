# Uniform 3-adic inverse sieve for Sheep's power-of-two halting gates

**Agent 14, 9 November 2026.** **Research status:** all-integer, all-exponent mathematical proof with a reproducible complete-period certificate derived from Sheep's original-source first-even transition equations. The entire new theorem has not been assembled as a single pinned-original-source Lean proof. These exclusions remain intermediate `im-results/` research pending independent review and external-priority comparison. No full Sheep blank-start decision or exact BB(6) value follows.

## Main theorem and quantitative advance

Let `E` be the authentic even-first-return relation of the six-state Sheep Turing machine `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` and `EvenReach` its reflexive-transitive closure. The original blank-start machine enters this section at state value **10**. Its halting condition is the eventual encounter of an even power of two.

For `0 ≤ s ≤ 16`, fix `r` with `1≤r≤63` and `3∤r`, and consider every integer `k≥0`. Define

```
n = 3^s * (r + 63*k),    j = 17496*n,    target = 2^j.
```

The [complete-period certificate](./stratum_certificate.py) finds a set `R_s` of residues `r` with **no incoming authentic even-return edge** into `target` for every `k`. Thus all these powers satisfy `¬ EvenReach 10 (2^j)`. This is a source-algebra mathematical exclusion with no time horizon or numerical tape simulation.

| s | Certified residues among 42 | s | Certified residues among 42 | s | Certified residues among 42 |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 30 | 6 | 12 | 12 | 10 |
| 1 | 30 | 7 | 12 | 13 | 20 |
| 2 | 12 | 8 | 30 | 14 | 20 |
| 3 | 30 | 9 | 12 | 15 | 20 |
| 4 | 30 | 10 | 25 | 16 | 8 |
| 5 | 30 | 11 | 25 | | |

The certified progressions are disjoint because each has an exact 3-adic valuation `v3(n)=s` and a distinct coprime residue `r` modulo 63. Their lower natural-density contribution **among positive integer indices `n` in `j=17496*n`** is exactly

```
sum(s=0..16) |R_s|/(63*3^s)
 = 1849545554/2711943423
 = 68.20000514443%.
```

This is a density of predecessor-free **exponent indices in this sparse subsequence**. It is not an estimate of the probability that the original machine halts. The unclassified high-valuation tail `v3(n)≥17` has natural density `3^(-17)≈7.74e-9`; classes left open within the first 17 strata can still have large unknown inverse cones. The result gives a rigorous **lower bound** on predecessor-free density; it does not establish the full exact density.

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

The finite modular calculation is a proof certificate: each small modular multiplication, modulus and period is explicitly checked by reproducible source. It is not yet a Lean-kernel result for the entire 17-stratum union.

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

## Reproduction and open obligation

Run `python stratum_certificate.py` (Python 3.10+), requiring only the standard library. The output lists every excluded `r` in each stratum and checks the complete modular orders, exceptional inequalities, row thresholds and the exact rational density. The fixed 17-element count vector is

```
[30,30,12,30,30,30,12,12,30,12,25,25,10,20,20,20,8].
```

The necessary remaining task for fully source-integrated formal certification is an original-machine Lean theorem incorporating the LTE bound, all complete modular finite residue checks, the existing high-`a` odd gap and the exceptional-source exclusion. The [pinned original-machine Sheep bridge](../agent16-sheep-even-return/README.md) and [even-edge inverse splitter](../agent14-sheep-even-inverse/SheepEvenSourceAlgebra.lean) already exist. Separately, a global invariant resolving genuine reachability of **all** powers from the blank seed is still needed to decide this machine and ultimately BB(6).

The independently attempted unrelated 31104 three-node inverse-chain source workflow failed before compilation because its Lean toolchain download received HTTP 504; it is not evidence for or against these new claims. The unmodified arithmetic certificates passed locally in Python.
