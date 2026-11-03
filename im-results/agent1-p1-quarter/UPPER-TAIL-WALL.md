# P1 inverse-cone affine wall: complete last-reset decomposition and root-only exclusion

**2026-11-03, Agent 1, programme R002.** Original-source Lean 4.36.0-rc2 manual [CI 41565894761](https://github.com/FlareZ123/bb6/actions/runs/41565894761) succeeded at source revision `3d2ee678c156848e6f297b18251c205561e9f9b5`. No `sorry`, new axioms, unverified source substitutions, or altered original recurrence. `#print axioms` on the final theorem reports the standard `[propext, Classical.choice, Quot.sound]`. The independently exact source theorem `UpperTail.lean` also passed [CI 41564983637](https://github.com/FlareZ123/bb6/actions/runs/41564983637). These are intermediate reductions: **no P1 root nonhalting decision or BB(6) bound improvement**.

## Mathematical setting

Let `q>=1`, `P=2^(16q)`, `u=7P-4q-3`. The two authentic P1 n=16q+2 critical feeders established by Agent45 are

- L0 `(4u-4,4u+9)` with wall offset `delta=12`;
- L1 `(6u-2,2u+5)` with wall offset `delta=16`.

The original `OddCone b0 d0 b d m` of `OddConeMass.lean` is the reflexive, arbitrarily long predecessor grammar whose edges are actual source `inverseAt` inverse branches with odd output and cost `t+1`. Agent9's authentic theorem `authentic_reachable_even_exponential_or_wall` states that any genuinely blank-reachable positive even-right terminal exit requires `m>=8P`, or depth `t=1` at the feeder-dependent affine wall `b=4m+64q+delta`. The present work concerns that remaining **synthetic cone wall membership**, independent of blank reachability.

## All-depth exact tail theorem

`UpperTail.lean` introduces `UpperTail b0 d0 m0 b d m n`, any chain of n consecutive exact inverseAt depth-zero edges, with the source's odd-sector conditions and positive source k. It proves, without any bound on n,

```
2^n * (b+12) = b0+12
m = m0+n
```

Consequently, if the tail ends on `b=4m+64q+delta` then necessarily

```
b0+12 = 2^n * (4*m0 + 4*n + 64*q + delta + 12).
```

`odd_cone_last_reset` proves by induction on the **original** `OddCone` that any cone path is exactly a consecutive upper tail from either (a) its original root or (b) the **last** positive-depth (`t>=1`) inverseAt edge on the path, with that edge's authentic predecessor cone retained. This is an existential decomposition of every finite source path, not a truncated search, and makes no claim that a synthetic inverse state is blank-reachable.

## Uniform exclusion of wall by an upper-only path

`RootWallArithmetic.lean` proves `no_initial_upper_wall`: for all q>=1, all n>=0, and both exact feeder roots, the tail wall equation above is impossible when the start equals the original feeder. This includes n=0 and arbitrarily long tails.

The arithmetic proof uses the exact root values

```
L0: (b0+12) + 16q+4 = 28P
L1: (b0+12) + 24q+8 = 42P.
```

For a putative wall `b0+12=2^n(4n+64q+delta+12)`, the coefficient on the right is at least 76 whereas the root's coefficient of P is at most 42. Thus n<16q. Since `2^n` then divides `P` and the wall expression, it must divide the nonzero correction `16q+4` (L0) or `24q+8` (L1). Thus `2^n<=24q+8<=32q`, and n<16q implies the wall expression is <=`(32q)(156q)=4992q^2`. Conversely the exact root identity implies `28P<=42P` and, using the all-q bound `P>=65536q^2`, the purported root equality forces an incompatible much larger lower bound. All quantifiers and arithmetic inequalities are encoded in Lean.

## New source-connected necessary reset condition

`WallReset.lean` combines the two theorems. Its final theorem `wall_requires_positive_reset` establishes for **any** original `OddCone` wall node, with no prior cost/depth limit, the existence of an authentic earlier source inverse

```
inverseAt bp dp t = some(k,c), t>=1, c odd, k>=2,
OddCone L0_or_L1 bp dp mp
```

and a natural n>=0 such that

```
2k+8 = 2^n * (4*(mp+t+1) + 4*n + 64*q + delta + 12).
```

Here `delta=12` for L0 and 16 for L1. The exact source-connected proof is [CI 41565894761](https://github.com/FlareZ123/bb6/actions/runs/41565894761). The equation is a new *necessary* test for any wall witness, and is directly compatible with Agent9's separate low-cost positive-depth lower bound (see `OddResetOriginal.lean`).

## Frontier and limits

The largest remaining questions are whether any authentic odd cone can satisfy that positive-reset dyadic equation for `m<8P`, and whether arbitrary exact cones can have `m>=8P`. Without excluding both alternatives, even-right exits in the n=16q+2 family remain unresolved. Exceptional c=1 exits and n=16q+14 have **separate** outstanding questions. No claim about the exact value of BB(6) follows.

A finite one-reset stress probe run locally over q=1..1000 for both roots produced no wall example, but its exact bounded sample is exploratory and does not establish a theorem. The next concrete source-connected pilot is to bound the 2-adic valuation of `2k+8` at a first positive-depth reset, exploiting the exact feeder equations `6u+10` or `5u+7`, rather than generating more independent residue certificates.
