# #746: exact return-map crosswalk with the DeepMind Cryptids acceleration

**Status:** exact algebraic crosswalk derived from the external `highLevelNext` definition and the local reset recurrence. The external machine reduction is Lean-formalized; this note's crosswalk has not yet been added to a Lean proof. It does not prove that the blank-root orbit avoids the fatal target.

## External formalization

The exact machine appears in Google's public `google-deepmind/cryptids` repository:

- [Machine module](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean)
- [Hardness summary](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/Hardness.lean)
- [Halting-family proofs](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/HardnessEvidence.lean)

Its state `.C a b` encodes the tape macro `C(a,b+1)`. The machine module proves `isHalt_iff_highLevel_acceleration`, so its high-level transition is an exact acceleration, not a heuristic simulation. The `.C a 1` state halts; the family `.C a (2*a+3)` reaches it in one transition.

The Hardness summary identifies the target family `4*2^n - n - 6` for its underflow parameter and reports a heuristic hazard estimate `~10^-294` after 1,253 cascades. That estimate is not a proof of nonhalting.

## Exact high-level cascade from `.C a 0`

The high-level map has these relevant branches:

- `.C a 0 -> .C 2 (2*a+1)`;
- for `.C a (d+2)`, if `d >= 2*a`, then `.C a (d+2) -> .C (2*a+2) (d-2*a)`;
- otherwise the underflow branch returns the quotient/remainder modulo four of `6*a+d+5` for odd d, or `6*a+d+8` for even d.

Starting at `.C a 0`, after i applications of the large branch the state is
[
  left(4cdot 2^i-2,;2a+9+2i-8cdot2^iight).
]
This follows by induction from `a_{i+1}=2a_i+2` and `b_{i+1}=b_i-2-2a_i`.

The large branch at index i is applicable exactly when
[
  a+i+5ge 8cdot2^i.
]
Thus the first underflow index is exactly the local first-failure level
[
  K=min{ige0:a+i+5<8cdot2^i}.
]

At i=K, put `d_K=b_K-2`. It is odd, and the underflow numerator simplifies to
[
  6(4cdot2^K-2)+d_K+5
  =16cdot2^K+2a+2K.
]
Consequently the returned state is
[
  left(4cdot2^K+leftlfloorrac{a+K}{2}ightfloor,;
        2((a+K)mod2)ight).
]

If `a+K` is even, this is immediately `.C(h',0)`, with
[
  h'=4cdot2^K+rac{a+K}{2},
]
the local even-reset formula.

If `a+K` is odd, put
[
  P=4cdot2^K+rac{a+K-1}{2}+3.
]
The underflow output is `.C(P-3,2)`. Write `P=2^t d` with d odd. In a state `.C(x,2)`, the underflow map on x is
[
  U(x)=leftlfloorrac{3x+4}{2}ightfloor
  =egin{cases}(3x+3)/2,&x	ext{ odd},\(3x+4)/2,&x	ext{ even}.end{cases}
]
Starting at `x_0=P-3=2^t d-3`, induction gives
[
  x_i=3^i2^{t-i}d-3quad(0le ile t).
]
For i<t, x_i is odd; x_t=3^t d-3 is even. The final step is therefore
[
  x_{t+1}=U(x_t)=rac{3^{t+1}d-5}{2}.
]
This is exactly the local odd-reset output. Hence the return map from one external `.C(a,0)` state to the next `.C(h',0)` state is exactly the local `Cstep` recurrence, including its valuation parameter t.

This is the exact cross-framework identity: the external large-branch/underflow acceleration and the local first-failure/odd-part recurrence enumerate the same reset heights.

## Exact halting target from `.C a 0`

The state after i large steps has second coordinate
[
  b_i=2a+9+2i-8cdot2^i.
]
It reaches the halting state `.C _ 1` exactly when
[
  2a+9+2i-8cdot2^i=1,
]
or
[
  a=4cdot2^i-i-4.
]
Conversely, for this value of a, the large branch applies at every earlier index and the state at index i has second coordinate 1. Thus the exact target for a `.C(a,0)` return state is
[
  a-2=4cdot2^i-i-6.
]
This is the target family in the external Hardness summary. In local reset notation the fatal height at level n is
[
  F_n=4cdot2^n-n-4,
]
so the two target descriptions agree under `a=F_n`.

The first local reset heights
[
  2,5,11,35,51,59,218,542,1181,2429,3267,3686,8768,ldots
]
match the `.C(a,0)` return heights of the external high-level map. This prefix is a cross-check; the algebra above gives the general return-map identity.

## Relation to the t=1 Q-parent equation

For a local odd reset with `t=1`, write `P=2d` with d odd. Its output is
[
  h'=rac{9d-5}{2},qquad h'-2=rac{9(d-1)}2.
]
At child level K+1 the deficit is
[
  D'=rac{32cdot2^K+2K+7-9d}{2}.
]
Set `c=2K+7` and `a=4*2^K-d`. Then
[
  2D'=9a+c-2^{K+2}.
]
The one-even-exit fatal condition `D'=c,2^j` is therefore exactly
[
  9a+c-2^{K+2}=c,2^{j+1},
]
the Q-index equation in the local t=1 dossier. The Q selector is the 3-adic coordinate of the underflow parent; the power-of-two quotient is the independent dyadic-tail condition.

The basic sector condition also follows immediately: any odd-reset output satisfies
[
  h'-2=3rac{3^t d-3}{2},
]
and the fraction is an integer because `3^t d-3` is even. Therefore a fatal target `F_n` reached directly after an odd reset must satisfy
[
  3mid(F_n-2)=4cdot2^n-n-6,
]
which holds exactly for `n mod 6 = 4 or 5`. For the adjacent t=1 route with n=K+2 this is `K mod 6 = 2 or 3`, agreeing with the local sector theorem.

For t≥1, the stronger factorization
[
  h'-2=9rac{3^{t-1}d-1}{2}
]
gives the corresponding 9-divisibility condition.

## Research consequence

The external and local formulations are now algebraically cross-walked:

1. The external `.C(a,0)` return map is the local `Cstep` reset recurrence.
2. The external underflow target `4*2^n-n-6` is the local fatal-height family shifted by 2.
3. The t=1 Q equation is exactly the dyadic-tail condition on one particular underflow parent.
4. The odd-reset factor of 3 explains the fatal-level sectors; t=1 strengthens this to divisibility by 9.

This does not resolve root avoidance. It does give future work a second exact coordinate system: the local problem can be attacked either as a first-failure/odd-part orbit avoiding `F_n`, or as the external high-level return map avoiding `.C(a,1)`. The remaining obstacle is the same joint 2-adic/3-adic target intersection, not a discrepancy between the two accelerations.
