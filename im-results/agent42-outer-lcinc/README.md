# TM63 outer `LC_Inc` reset-prefix: counted source decomposition

**Status: computationally discovered and exhaustively checked on a finite parameter grid; not yet a Lean theorem.** This belongs in `im-results/`, not `results/`.

## Candidate exact transition

For the source-exact encoder in `im-results/agent8-s1-encoder/S1Encoder.lean`, let

`s1Config L n m a 0 b h`

be the S1 configuration with outer binary counter (n>0), marker (m\in\{0,1,2\}), unary counter (a), inner counter zero, and right counter (b). The TM63 reset prefix appears to satisfy

[
\operatorname{run}_{TM63}\bigl(12a+63+4m+3b+12v_2(n)\bigr)
  (S1(L,n,m,a,0,b,h))
=
S1\!\left(L,n-1,(m+2)\bmod 3,,
a+b+\delta_m,,2^b-1,,0,,h+3b+5\right),
]

where
[
\delta_0=1,\qquad \delta_1=\delta_2=2.
]

This is exactly the already-defined `resetPrefixCost m n a b` in `im-results/agent8-counted-reset/CountedReset.lean`. The endpoint parameters agree with the three Coq macros:
- (m=0\): (m'=2), (a'=a+b+1);
- (m=1\): (m'=0), (a'=a+b+2);
- (m=2\): (m'=1), (a'=a+b+2).

## Useful structural factorization

The trajectory has a particularly useful three-part split. Put (r=v_2(n)).

1. **Source prelude:** (9a+3m+17) steps, ending in state D at
   [
   h_1=h-(3a+m+5).
   ]
   At this point the tape satisfies the hypotheses of Agent 24's existing
   `counted_LBinDec_HRun` theorem:
   - `leftOnes T h1 (3*r)`;
   - (T(h_1-3r)=false);
   - (T(h_1-3r-1)=false);
   - (T(h_1+1)=false).

2. **Outer binary decrement H-run:** (12r+4) steps. This is the exact
   `counted_LBinDec_HRun` macro already proved in
   `im-results/agent24-champion-time/CountedLBinDecHRun.lean`. It ends in
   state B at (h_1+2).

3. **Return/transfer postlude:** (3a+42+m+3b) steps, ending at the target
   S1 configuration above.

The costs add:
[
(9a+3m+17)+(12r+4)+(3a+42+m+3b)
=12a+63+4m+3b+12r.
]

This factorization isolates the existing universally proved H-run in the
middle. The remaining Lean obligations are the parameterized source-prelude
frame and the return/transfer postlude from the H-run endpoint.

## Evidence and limits

`verify_outer_lcinc.mjs` simulates the original six-state transition table
against the S1 tape encoding. It checks all intermediate H-run hypotheses,
the B-state/H-run endpoint, the final D-state/head, and the complete finite
support of the target tape.

The checked grid is:
- (L=2,3,4,5);
- (1\le n<\min(2^L,16));
- (m=0,1,2);
- (0\le a\le4);
- (0\le b\le3).

That is 2,400 parameter tuples, with zero mismatches. The root-relevant sample
((L,n,m,a,b)=(3,7,2,6,63)) gives a 332-step prefix and the exact endpoint
((3,6,1,71,2^{63}-1,0,h+194)).

This is computational evidence only. It does not prove the universal
prelude/postlude lemmas, does not establish a BB(6) upper bound, and must not
be promoted to `results/` until the parameterized Lean proof compiles and its
axioms are checked.


## Prelude factorization

The source prelude splits again without any fitted arithmetic:
- the initial S1 tape has `leftOnes T h (3*a)` because `binDec a 0 = d1pow a`;
- its immediate right neighbor is zero;
- Agent 24's `counted_left_sweep` therefore proves the first (9a) steps and moves the D head to (h-3a);
- a fixed marker/boundary bridge of (3m+17) steps then places the D head at (h_1=h-(3a+m+5)).

Thus the only parameter-dependent part of the prelude after the existing sweep is a small three-case ((m=0,1,2)) local trace. The outer `binDec L n` is then exposed directly to the existing H-run theorem.
