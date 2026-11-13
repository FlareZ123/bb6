# Correlated dyadic-cylinder moments and first survival sets

This is an intermediate P1 shadow-tree result, not a BB(6) solution and not yet a source-lift theorem.

## Exact cylinder structure

For a depth-`d` word `w=(t_1,...,t_d)`, put
`M(w)=sum_i (t_i+1)`.  The affine cylinder constructors in
`finite_cylinder_regression.py` give a single 2-adic cylinder
`C_w = {q : q = q_w mod 2^h}`, with

- feeder 8: `h=M(w)-2`;
- feeder 9: `h=M(w)-1`.

The offset is constant under each child extension because both the total
cost and cylinder level increase by `t+1`.  Thus two word cylinders are
disjoint or nested.

For a finite multiset of cylinders, let `m(C)` be the multiplicity of
exactly the cylinder `C`, and let `a(C)` be the sum of multiplicities of
its strict ancestors.  If `N(q)` counts words valid at `q`, then the exact
second-moment identity is

```
E[N^2] = sum_C 2^(-level(C)) * (m(C)^2 + 2*m(C)*a(C)).
```

This follows by expanding `N^2`: equal cylinders contribute `m(C)^2`,
and every strict nested pair contributes twice the measure of its smaller
cylinder.  It is important not to replace the tree by an independent
Galton-Watson process.

## Rigorous truncation bound

The number of length-`d` words of total cost `M` is
`binom(M-1,d-1)`.  If any edge depth exceeds cutoff `T`, then
`M >= T+d+1`.  Since the intersection of two cylinders is at most the
smaller cylinder measure, the omitted second-moment contribution is at most

```
2^(c+1) * sum_{M >= T+d+1}
  binom(M-1,d-1) * binom(M,d) * 2^(-M),
```

where `c=2` for feeder 8 and `c=1` for feeder 9.  The series converges
for every fixed depth.  The executable script replaces it by a rational
geometric-majorant bound.

## Certified second moments

The following are exact finite-cutoff values.  The unrestricted second
moment lies between the displayed value and that value plus the stated
rational tail bound.

| Feeder | Depth | Cutoff | Exact truncated second moment | Tail upper bound |
|---|---:|---:|---:|---:|
| 8 | 2 | 64 | 2413440587313935624280713453290029126013 / 340282366920938463463374607431768211456 | < 1.71e-14 |
| 9 | 2 | 64 | 4905472539199644719376277096260007499563 / 680564733841876926926749214863536422912 | < 8.55e-15 |
| 8 | 3 | 48 | 434276355732934266607051527448556537579236723 / 44601490397061246283071436545296723011960832 | < 1.26e-7 |
| 9 | 3 | 48 | 871299944319034015450233541331664650750300131 / 89202980794122492566142873090593446023921664 | < 6.26e-8 |

Decimal values are approximately 7.092464441081888, 7.2079440724288055,
9.73681264609822, and 9.767610191524488 respectively.  These are
correlated second moments, not Galton-Watson predictions.

The truncated first moment is checked exactly against

- feeder 8: `(2-2^(1-T)) * (1-2^(-(T+1)))^(d-1)`;
- feeder 9: `(2-2^(-T)) * (1-2^(-(T+1)))^(d-1)`.

Its limit is 2 for each fixed depth.

## First exact survival probabilities

Let `E_d` be the set of `q in Z_2` for which at least one depth-`d`
shadow word exists.

For depth 2:

- feeder 8: `E_2 = {q even} union {q = 1 mod 4}`;
- feeder 9: `E_2 = {q odd} union {q = 2 mod 4}`.

In each case the complement is one residue class modulo 4, so
`mu(E_2)=3/4`.

For depth 3, both feeders have exactly
`E_3 = {q = 1 or 2 mod 4}`, hence `mu(E_3)=1/2`.

Witness cylinders covering this set are:

- feeder 8: `q=2 mod 4` via word `(1,0,0)`;
  `q=1 mod 8` via `(1,1,0)`;
  `q=5 mod 16` via `(1,1,1)`;
  `q=13 mod 16` via `(1,2,0)`.
- feeder 9: `q=1 mod 4` via `(0,0,0)`;
  `q=2 mod 8` via `(0,1,0)`;
  `q=6 mod 16` via `(0,2,0)`;
  `q=14 mod 16` via `(0,1,1)`.

For the reverse inclusions, the two excluded classes are checked directly
from the root valuation.  Feeder 8: if `q=3 mod 4`, the root has
valuation 3 and only depth 1 is legal; its child has valuation 1 and no
child.  If `q=0 mod 4`, the root has valuation 2; its only legal depths
are 1 and 2, and both child states have odd offset and type 1, hence no
further child.  Feeder 9: if `q=0 mod 4`, the root has valuation 2 and
only depth 0 is legal; its child has valuation 1 and type 0, hence no
child.  If `q=3 mod 4`, the root has valuation 1 and legal depths 0 and
1; the depth-0 child has one child whose child has odd offset and type 1,
while the depth-1 child has odd offset and type 1 immediately.  Thus neither
root branch reaches depth 3.

The script `second_moment_census.py` reproduces the exact cylinder
enumeration, multiplicities, moments, and rational tail bounds.  Use
`--exploratory` for higher-depth survival intervals.  These results concern
the abstract shadow feeder graph; the existing source-to-shadow bridge is
still one-way, so do not silently promote them to original-source statements.
