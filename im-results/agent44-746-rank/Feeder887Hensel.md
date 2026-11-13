# The 887 common feeder and its exact 3-adic isometry

**Status:** exact arithmetic derivation from the complete `ResetParent` grammar, not yet Lean source-compiled. The uniform common-parent path below is mathematically valid for every `n % 13122 = 887`; the valuation/isometry theorem is unconditional for its displayed scalar function. This is an intermediate result, not a blank-root decision.

## 1. Uniform common path

Use the notation of `CascadeFeeder887SecondTier`:

```
p  = 2^(n-2)
T  = 80*p - 4118*n - 6123
z2 = 12*(T/243) - (2*p+n+1)
```

For `n % 13122 = 887`, the existing period calculation gives
`n % 6561 = 887` and `p % 6561 = 3869`. In particular
`T % 729 = 486`, so `243 | T`; reducing one level further gives
`p % 2187 = 1682`, `T % 2187 = 1215`, and
`(T/243) % 9 = 5`. The exported wrapper
`z1_unique_parent_887` on Agent 10's PR #80 branch derives its internal
`hTmod : T % 729 = 486` from the index congruence; the core theorem
`z1_unique_parent` takes `hTmod` as a premise, but the all-index wrapper
does not leave it as an external hypothesis.

The exact even-parent map at scale `n-4` is
`E(u) = 2*u - 2*p - n + 4`. Define `u_0=z2` and
`u_(i+1)=E(u_i)`. Direct substitution gives

| state | exact value |
|---|---|
| `u0` | `(158*p - 16553*n - 24573)/81` |
| `u1` | `(154*p - 33187*n - 48822)/81` |
| `u2` | `(146*p - 66455*n - 97320)/81` |
| `u3` | `(130*p - 132991*n - 194316)/81` |
| `u4` | `(98*p - 266063*n - 388308)/81` |

For the first odd parent, put
`v1=(2*u4+5)/3` and `w5=2*v1-p-n`. For the second, put
`v2=(2*w5+5)/3` and `h=2*v2-p/2-n+1`. Their exact formulas are

| state | exact value |
|---|---|
| `v1` | `(196*p - 532126*n - 776211)/243` |
| `w5` | `(149*p - 1064495*n - 1552422)/243` |
| `v2` | `(298*p - 2128990*n - 3103629)/729` |
| `h` | `(463*p - 8517418*n - 12413058)/1458` |

### Why all six edges exist for every index in the subresidue

A simple strengthened growth bound suffices:
`p=2^(n-2) >= 100000*n` for every `n>=887`. At n=887 this follows from
`2^885 >= 2^27 > 100000*887`; the induction step follows by doubling.

The even-band conditions for `u0,u1,u2,u3` at scale `n-4` reduce,
respectively, to the following lower inequalities; the upper inequalities
are immediate from the displayed affine formulas:

```
73*p >= 33106*n + 48984
65*p >= 66374*n + 97482
49*p >= 132910*n + 194478
17*p >= 265982*n + 388470
```

The odd-band conditions for `v1` at scale `n-5` and `v2` at scale
`n-6` reduce to

```
55*p >= 2128504*n + 3105816
197*p >= 17031920*n + 24834864
```

and their upper bounds are again immediate. All six lower inequalities
follow from `p >= 100000*n` and `n>=887`.

The divisibility and parity conditions are also uniform. Since
`n % 9 = 5`, `p % 9 = 8`, and `(T/243) % 9 = 5`, we get
`u0 % 9 = 2`. The even-parent recurrence has
`u_(i+1) = 2*u_i - 2*p - n + 4 ≡ 2*u_i+1 (mod 9)`, so
`u1,u2,u3,u4 ≡ 5,2,5,2 (mod 9)`. Hence `9 | 2*u4+5`, in particular
the first t=0 odd quotient `v1` is integral. Also `v1 % 3 = 0`, so
`w5 = 2*v1-p-n ≡ 2 (mod 3)`, and the second t=0 quotient `v2`
is integral. The numerator `T` is odd, hence `T/243` is odd and
`u0` is even; each even-parent output is odd. Thus `u4` is odd,
`v1` is odd, `w5` is odd, and `v2` is odd. These are exactly the
odd-quotient parity requirements in `ResetParent`. The band lower bounds
also make all three parent outputs nonnegative.

Consequently the complete source grammar contains, uniformly in the
subresidue, four even edges followed by two t=0 odd edges:

```
z2 -> u1 -> u2 -> u3 -> u4 -> w5 -> h.
```

This proves the path formula algebraically, conditional on the
`z2` coordinate supplied by Agent 10's uniform second-tier unique-parent
draft. That draft is not yet source-CI-verified. It is not a claim that this path is the whole
reverse cone: `h` can have additional odd parents.

Composing the formulas yields the key identity

```
1458*h = 463*p - 8517418*n - 12413058
729*(2*h+5) = 463*p - 8517418*n - 12409413.
```

Thus Agent 10's proposed numerator is not merely a numerical fit: it is
the exact affine composition of the six displayed parent maps, once the
uniform band/divisibility checks above are supplied.

## 2. Exact 3-adic isometry

Write `n=887+13122*r`, so `p=2^(885+13122*r)`, and define

```
F(r) = 463*2^(885+13122*r)
       - 8517418*(887+13122*r) - 12409413.
G(r) = F(r)/3^8.
```

The quotient `G(r)` is an integer for every natural `r`. Indeed,
`A=2^13122=4^6561` satisfies
`v3(A-1)=v3(4^6561-1)=1+v3(6561)=9` by LTE.
Also `F(0) ≡ 13122 (mod 19683)`, so `3^8 | F(0)`; and
`F(r)-F(0)` is divisible by `3^8).

More strongly, for all distinct natural `r,s`,

```
v3(F(r)-F(s)) = 8 + v3(r-s),
v3(G(r)-G(s)) = v3(r-s).
```

To see this, assume `r>s` and put `d=r-s`. Then

```
F(r)-F(s)
 = 463*2^885*A^s*(A^d-1) - 8517418*13122*d.
```

LTE gives `v3(A^d-1)=9+v3(d)`, so the first term is divisible
by `3^(9+v3(d))`. The second term has *exactly*
`8+v3(d)` factors of 3, because `3 ∤ 8517418` and
`13122=2*3^8`. There can be no cancellation at that lower
valuation. This proves the displayed equality.

Therefore `G` is an isometry of the 3-adic integers. Modulo every
`3^k` it is injective, hence bijective on the finite residue ring.
There is exactly one compatible residue `rho_k (mod 3^k` satisfying

```
G(rho_k) = 0 (mod 3^k)
F(rho_k) = 0 (mod 3^(k+8)).
```

For every natural `r`, the exact valuation is determined by this
single compatible 3-adic root:
`v3(G(r))` is the largest `k` for which
`r ≡ rho_k (mod 3^k)`. Since `F=729*(2*h+5)` and
`G=F/6561=(2*h+5)/9`, this becomes

```
v3(2*h(r)+5) = 2 + v3(G(r)).
```

Thus the possible odd-parent exponents at `h(r)` are bounded exactly
by `t <= 1 + v3(G(r))`; the dyadic band test must still decide which
of those divisibility candidates are genuine parents.

The first exact Hensel residues, computed by testing the three possible
next digits at each lift, are:

| k | unique `rho_k mod 3^k` | new ternary digit |
|---:|---:|---:|
| 1 | 1 | 1 |
| 2 | 4 | 1 |
| 3 | 13 | 1 |
| 4 | 13 | 0 |
| 5 | 13 | 0 |
| 6 | 499 | 2 |
| 7 | 1228 | 1 |
| 8 | 1228 | 0 |
| 9 | 14350 | 2 |
| 10 | 14350 | 0 |
| 11 | 132448 | 1 |
| 12 | 486742 | 2 |

The residues are compatible under reduction (for example,
`499 % 243 = 13`, `1228 % 729 = 499`,
`14350 % 6561 = 1228`). They explain the observed examples:
`r=0` has `v3(2h+5)=2`; `r=1` has valuation 3; and
`r=13` agrees with `rho_5=13` but not `rho_6=499), giving
valuation 7. These match the exact-integer scans.

## 3. Consequences and limits

1. The fixed six-/ten-node n=887 cone is not uniform over all
   `n=887+13122*r`: the 3-adic isometry proves that arbitrarily high
   divisibility thresholds are organized by nested unique residue classes,
   and the scan already exhibits t=2 and t=5 extra branches.
2. The scalar selector is cleaner than a finite residue census. It gives
   an exact all-precision classification of the divisibility of the
   common feeder's odd-parent numerator.
3. Divisibility is not band membership. For each permitted exponent,
   the exact odd-band window and the descendant's own parent tree still
   have to be handled. The result does not establish global nonreachability
   of the fatal target, and does not decide the #746 machine or BB(6).
4. The next formalization should prove the six uniform `ResetParent`
   edges and the valuation-isometry theorem in Lean, then combine the
   unique Hensel residue at each precision with the existing exact
   dyadic-band envelope to classify all additional parents of `h`.

## Source pointers

- `im-results/agent10-cascade/FirstInverseComplete.lean`: exact two-arm
  `ResetParent` grammar.
- Agent 10 PR #80, branch
  `agent10/two-tier-depth-selector-20261113`:
  `Z1UniqueParent887.lean`; in particular
  `z1_unique_parent_887` derives `hTmod` uniformly from
  `n % 13122 = 887`.
- `im-results/agent10-cascade/887-family-cone-scan.md` and
  `scan_887_family_cones.py`: original discovery and reproducible
  exact-integer samples. The algebra and 3-adic isometry above strengthen
  that exploratory note; this file is not yet a Lean source proof.


## 4. Unbounded odd fan-in across the 887 family

The isometry gives more than unbounded divisibility: combined with the
dyadic band, it proves that the number of *distinct actual odd parents*
of the common feeder is unbounded as the index varies.

For t>=1, when `3^(t-1) | G(r)`, define

```
d_t = G(r)/3^(t-1)             (odd)
x_t = 2^t*d_t = 2^t*G(r)/3^(t-1).
```

Since `2*h(r)+5=9*G(r)`, we have
`2*h(r)+5 = 3^(t+1)*d_t`. Thus an odd ResetParent of exponent t
exists exactly when `x_t` belongs to an odd dyadic band
`[6*2^k+1, 8*2^k-1]`; its source state is

```
q_t = 2*x_t - 8*2^k - k - 5.
```

Let S be the set of t>=1 for which some integer j satisfies the strict
limiting band window

```
6 < 463*2^(t+j) / (6561*3^(t-1)) < 8.
```

For each t in S, the scale is unique because the band width ratio is
8/6=4/3<2. The first pairs (t,j) are

```
(2,6), (5,8), (7,9), (10,11), (12,12), (15,14),
(17,15), (19,16), (22,18), (24,19), (27,21), (29,22), ...
```

The set S has natural density log2(4/3). Indeed, taking logarithms,
the condition is that some integer j places

```
j + log2(463/2187) - t*log2(3/2)
```

inside the interval (log2(6), 3), whose length is log2(4/3).
The rotation step log2(3/2) is irrational (a rational value would imply
a nontrivial equality between powers of 2 and 3), so the fractional
parts are equidistributed. In particular S is infinite and has positive
density.

Now fix T and choose r in the Hensel class
`r ≡ rho_(T-1) (mod 3^(T-1))`. There are infinitely many such r.
The isometry gives `3^(T-1) | G(r)`, so every t in S with t<=T
has an odd quotient d_t. Along this arithmetic progression, as r tends
to infinity,

```
G(r)/p -> 463/6561,
x_t/p -> 463*2^t / (6561*3^(t-1)).
```

For each of the finitely many t in S∩[1,T], the defining strict
limiting window therefore becomes the actual band condition at
`k_t=n-2-j_t` for all sufficiently large r in the chosen Hensel
class. Choose one r large enough for all these finitely many
conditions simultaneously. Then every such t gives a genuine
`ResetParent(q_t,h(r))` edge.

These parent states are distinct. For fixed h,
`x_(t+1)=2*x_t/3`, so x_t strictly decreases with t. At a band
scale k, the corresponding parent lies in

```
4*2^k-k-3 <= q_t <= 8*2^k-k-7.
```

The parent intervals for adjacent scales are disjoint: the upper
endpoint at scale k-1 is `4*2^k-k-6`, strictly below the lower
endpoint `4*2^k-k-3` at scale k. Hence different scales give
different parents; at the same scale, strict decrease of x_t gives
different parents as well.

It follows that for every T there is an index n in the subresidue for
which h(r) has at least `|S∩[1,T]|` distinct odd ResetParent
predecessors. Since `|S∩[1,T]| ~ log2(4/3)*T`, the odd fan-in of
the common feeder is unbounded across the family. Conditional on the
upstream `z2` parent theorem, these are also distinct nodes in the
fatal candidate's reverse cone.

This rules out any fixed finite-width inverse-cone certificate that is
claimed to work uniformly over all `n=887+13122*r`. It does **not**
rule out a parameterized proof: the Hensel selector and the irrational
rotation together describe exactly why the finite cone width grows.
The result remains an unformalized mathematical derivation; a Lean
source proof of the common path and isometry is still required.


## 5. Unbounded even-chain depth in the same family

The same irrational rotation also forces arbitrarily long *even-parent
continuations* below some of the odd parents counted above.

For t in S, let j_t be its unique scale offset and set

```
R_t = 463*2^(t+j_t) / (6561*3^(t-1)),   6 < R_t < 8.
```

The sequence R_t is dense in (6,8): the translated logarithms
`j_t + log2(463/2187) - t*log2(3/2)` are dense in
`(log2(6),3)`.

Fix such a t and choose r in the Hensel class as in section 4, large
enough that the first odd parent q_0 exists at scale
`k=n-2-j_t). Define its repeated even parents at the *same* scale by

```
q_(m+1) = 2*q_m - 8*2^k - k.
```

For each fixed m, as r tends to infinity along that Hensel progression,

```
q_m / 2^k -> 8 - 2^(m+1)*(8-R_t).
```

This follows from `q_0/2^k -> 2*R_t-8`, `k/2^k -> 0`,
and the affine recurrence. The limiting ratios decrease with m.
Consequently the first m targets `q_0,...,q_(m-1)` all lie strictly
inside the even band (6,8) in normalized coordinates exactly when

```
R_t > 8 - 2^(1-m).
```

If this strict inequality holds, sufficiently large r makes all m
integer band conditions hold simultaneously, yielding m consecutive
genuine even ResetParent edges below q_0. The states are distinct
because the even-parent map strictly decreases a target inside the
band.

Since R_t is dense in (6,8), for every m there is t in S with
`R_t > 8 - 2^(1-m)`. Choosing r sufficiently large in the compatible
Hensel class gives an actual branch with at least m consecutive even
parents. Thus reverse-cone depth, as well as immediate odd-parent
fan-in, is unbounded across this subresidue.

There is also a quantitative density refinement. For fixed m>=1, the
set of t in S whose limiting mantissa satisfies
`R_t > 8-2^(1-m)` has natural density

```
delta_m = log2(8/(8-2^(1-m)))
       = -log2(1-2^(-m-2)).
```

This follows because the same irrational rotation is equidistributed
and the corresponding logarithmic window is
`(log2(8-2^(1-m)),3)`. Hence for every fixed m, a positive-density
set of exponents t admits m consecutive even-parent edges. Moreover,
for every finite T, one sufficiently large r in the Hensel class
`rho_(T-1) mod 3^(T-1)` realizes all such t<=T simultaneously:
the odd-band and all m even-band inequalities are finitely many
strict limiting inequalities, so one large r satisfies them all.
Thus there are feeders with at least
`delta_m*T+o(T)` distinct odd parents, each supporting m further
even-parent steps. As m grows,
`delta_m ~ 2^(-m-2)/ln(2)`.

The first examples from exact rational windows are:

| t | j_t | R_t (decimal) | consecutive even parents |
|---:|---:|---:|---:|
| 2 | 6 | 6.021846263 | 0 |
| 5 | 8 | 7.137002979 | 1 |
| 7 | 9 | 6.344002648 | 0 |
| 10 | 11 | 7.518817953 | 2 |
| 12 | 12 | 6.683393736 | 0 |
| 15 | 14 | 7.921059243 | 4 |
| 17 | 15 | 7.040941549 | 1 |
| 19 | 16 | 6.258614710 | 0 |
| 22 | 18 | 7.417617434 | 1 |
| 24 | 19 | 6.593437719 | 0 |
| 27 | 21 | 7.814444704 | 3 |
| 29 | 22 | 6.946173071 | 0 |

This is another obstruction to any fixed finite reverse-cone template.
It still leaves a viable parameterized route: classify the 3-adic
divisibility class, the unique dyadic scale, and the even-chain length
as functions of t and the Hensel digits.