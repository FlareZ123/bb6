# Exact second-tier odd-parent classification for the 887 lift

Status: algebraically derived from the existing 887-family formulas; the final source-parent theorem is not yet Lean-certified. This is deliberately narrower than a blank-root exclusion.

## Existing state coordinates

Use the notation of `CascadeEvenParent887` in Agent 7's `EvenParent887.lean`:
```
p  = 2^(n-2)
z0 = (56*p - 1025*n - 1551)/9
z1 = (40*p - 2059*n - 3084)/9
n % 13122 = 887
```
Here `z0` is the t=1 parent of the sixth canonical ray state, and `z1` is its even parent. The already-proved growth bound is `10000*n+10000 <= p`.

The two-tier numerator for `z1` is
```
T = 9*(2*z1+5) = 80*p - 4118*n - 6123.
```
The 887-family period calculation gives `n % 6561 = 887` and `p % 6561 = 3869`. Hence
```
T % 243 = 0
T % 729 = 486
```
so `v3(T)=5` exactly. In particular, with `d = T/243`, we have
```
2*z1+5 = 27*d,   d odd,   729 ∤ T.
```

## Complete classification of the odd inverse exponent at z1

In the odd disjunct of `ResetParent h z1`, the equation
`2*z1+5 = 3^(t+1)*e` and `729 ∤ T` force `t <= 2`. The only possible exponents are therefore 0, 1, 2.

Writing `d=T/243`, their odd-band arguments `x=2^t*e` are:
```
t=0: x = 9*d = T/27
t=1: x = 6*d = 2*T/81
t=2: x = 4*d = 4*T/243
```

The t=0 candidate is in the dyadic gap
```
2*p < T/27 < 3*p,
```
which is `4*2^(n-3) < x < 6*2^(n-3)`. The two inequalities reduce to
```
26*p > 4118*n + 6123,
T < 81*p,
```
and follow from the existing growth bound.

The t=2 candidate is in the gap
```
p < 4*T/243 < 3*p/2,
```
which is `4*2^(n-4) < x < 6*2^(n-4)`. These reduce to
```
77*p > 16472*n + 24492,
89*p + 32944*n + 48984 > 0.
```
Thus the generic `CascadeFeederExceptional.odd_gap` lemma excludes t=0 and t=2 for every possible band scale.

The t=1 candidate is in the actual odd band at scale `n-4`:
```
6*2^(n-4)+1 <= 2*T/81 <= 8*2^(n-4)-1.
```
The lower inequality reduces to `77*p >= 16472*n + 24654`; the upper inequality is immediate. The growth bound `p >= 10000*n+10000` is more than sufficient.

Therefore the only odd ResetParent of `z1` is the t=1 parent
```
z2 = 12*d - 2*p - n - 1
   = (158*p - 16553*n - 24573)/81.
```

## Even-parent exclusion at z1

The formula for z1 and the growth bound also give
```
4*p <= z1 < 6*p - 1.
```
Since `p=2^(n-2)`, this places `z1` in the middle-low gap
`(4*2^(n-2)-3, 6*2^(n-2)-1)`. The existing `no_even_band_from_gap` argument excludes every even ResetParent scale. Thus, subject to formalizing the displayed algebra, z2 is the **unique** ResetParent of z1.

## Next formalization

Add a theorem in the 887 even-parent module proving
```
(∀h, ResetParent h (z1 n) → h = z2 n)
```
using the exact valuation, `odd_gap`, and the middle-low even-band exclusion. Then analyze the small reverse subtree of z2. For n=887 its exact parent tree has 10 distinct states, with a terminal odd branch and a remaining even/odd chain; do not extrapolate that finite observation to the entire 887 family without proving the corresponding uniform parent identities and band inequalities.

This closes only the z1 predecessor classification. It does not close the full evenPre cone, whose main ray has many other odd branches.
