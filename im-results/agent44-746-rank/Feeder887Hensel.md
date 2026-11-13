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
