# Agent 5: halting funnel in a 2026 BB(6) high-level map

**Status: intermediate mathematical result.** This is an exact infinite family inside a certified unresolved acceleration. It does not show that the blank-tape orbit enters the family and does not decide the machine or BB(6).

Target machine:

`1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`

Source: Google DeepMind Cryptids,
`BusyBeaver/BB6/M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE.lean`.
The upstream file proves a high-level acceleration on states `E(b,d)` starting from `E(0,1)`, and proves its equivalence to the original blank-tape Turing-machine halting question. This acceleration was among the 2026 discoveries reported by the Cryptids project.

## Coordinate exposing the halt gate

Set

`t = d - 2b`

when this difference is nonnegative. Since the upstream map uses `c=d+1`, its remainder `c-2b` equals `t+1`. In these coordinates the low-remainder branch has:

* `t=0` or `t=1`: reset to first coordinate zero;
* `t=2`: halt;
* `t=3,4,5`: a short odd-output branch;
* `t>=6`: the affine branch
  `(b,t) -> (2b+4, t-4b-14)`.

The complementary `b>d/2` cases correspond to negative `t`; their outputs have odd `t`. Thus positive-even `t` episodes are isolated and can only move through the affine `t>=6` branch until reaching a small remainder.

## Exact recursive halting funnel

Define

`
H(0,b) = 2
H(n+1,b) = 4b + 14 + H(n,2b+4).
`

Then `Funnel.lean` proves, for every natural `n,b`:

`
E(b, 2b + H(n,b))
`

takes exactly `n` surviving high-level steps to a state with `t=2`, and the following high-level call halts.

For `b=0`, elementary solution of the affine recurrence gives

`
H(n,0) = 16*2^n - 2n - 14.
`

The first values are

`
2, 16, 46, 108, 234, 488, 998, 2020, 4066, 8160, 16350, ...
`

The Lean proof uses the recursive definition directly, avoiding any dependence on the closed-form algebra.

The upstream `t=0` and `t=1` reset branches enter `E(0,H(n,0))` exactly when

`
4b+4 = H(n,0)    (source t=0)
4b+6 = H(n,0)    (source t=1).
`

The attached file kernel-checks these entry lemmas too.

Solving the equations gives the explicit dangerous source families:

* source `t=0`, odd `n`: `b = (H(n,0)-4)/4`, beginning
  `3, 26, 121, 504, 2039, 8182, 32757, 131060, ...`;
* source `t=1`, even `n>=2`: `b = (H(n,0)-6)/4`, beginning
  `10, 57, 248, 1015, 4086, 16373, 65524, 262131, ...`.

## Blank-orbit screen

An exact 10,000,000-step simulation of the published high-level map from `E(0,1)` did not halt. It encountered ten `t in {0,1}` source states, all with `t=1`; their `b` values were

`
0, 114, 748, 1468, 2556, 3026, 9452, 13258, 113546, 2747338.
`

None is in the dangerous source family. This is finite evidence only.

The next research target is the return map on `t=1` source states. A proof that the blank-tape return sequence avoids the explicit exponential family above would eliminate this entire halting funnel. A proof that it hits one would decide this holdout as halting.

## Verification

`Funnel.lean` compiles with Lean 4.36.0-rc2. The printed axiom dependencies are only standard Lean axioms `propext` and `Quot.sound`; there is no `sorryAx`.

The standalone file copies the published high-level transition function exactly. The original-TM bridge itself remains the upstream DeepMind theorem.
