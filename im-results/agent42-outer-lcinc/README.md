# TM63 outer `LC_Inc` reset-prefix: counted source decomposition

**Status: the universal original-TM2 run theorem to the nested frame exists, and a full pointwise canonical-endpoint proof has now been drafted in `OuterLCIncCanonicalEndpoint.lean`; the new module is uncompiled and unaccepted.** This remains intermediate work in `im-results/`, not a publishable result.


## Current formal status (2026-11-18)

The earlier status above is superseded in one important respect: the source-run
itself is now formalized. `OuterLCIncPostludeSource.lean` exports
`outerLCInc_full_run`, a parameterized successful run from
`s1Config L n m a 0 b h` to the exact nested
`outerLCIncPostludeTape` frame, with cost

[
12a+4m+63+12v_2(n)+3b.
]

This is stronger than the original finite-grid evidence: the machine execution
and its primitive-step count are stated uniformly for positive valid source
counters. The remaining gap is not the run trace; it is the pointwise
identification of the nested output tape with the canonical S1/S0 encoder.

For the root-relevant `m=2,n=1` branch, the exact cost is
`12*a+71+3*b`, and the intended canonical endpoint is

```lean
s1Config L 0 1 (a+b+2) (2^b-1) 0 (h+3*b+5)
```

—not marker 0. The already-proved
`outerLCInc_target_binary_prefix` supplies

```
binDec (a+b+2) (2^b-1) = d0pow b ++ d1pow (a+2)
```

The new intermediate file
`OuterLCIncCanonicalEndpoint.lean` now contains the full pointwise
endpoint proof chain, beginning with
`outerLCIncSourceT3_leftFacing_m2` for the zero-valuation H-run and ending
with `outerLCIncPostludeTape_eq_marker1S0_m2`. **The entire file has not
been Lean-compiled**; none of its declarations is yet a verified theorem.

The endpoint proof has now been written as a source-level candidate in
`OuterLCIncCanonicalEndpoint.lean`. It exports the following chain:

1. `outerLCIncSourceT3_leftFacing_m2`: the zero-valuation H-run changes
   `binDec L 1 = d0 ++ d1pow(L-1)` into `binDec L 0 = d1pow L`
   at the far-left tail.
2. `outerLCIncAfterZero_leftFacing_m2`: the E-scan, five-step marker
   frame, H-run bridge, and two-step zero boundary yield
   `d1pow(a+2) ++ markerWord 1 ++ d0 ++ d1pow L ++ lh`.
3. `outerLCIncAfterSweep_leftFacing_m2`: the B/F/D sweep adds exactly
   `d0pow b`, proved by the three residues modulo 3 and the boundary one
   at `h+6`.
4. `outerLCIncPostludeTape_leftFacing_m2` and
   `outerLCIncPostludeTape_rightFacing_m2`: the fixed tail frame yields
   `s0RightFacing 0` at offsets +1 through +9, while the exterior from
   +10 remains blank.
5. `outerLCIncPostludeTape_eq_s1Config_m2`: combines both sides with
   `outerLCInc_target_binary_prefix` and the S1 encoder cell lemmas to
   identify the complete nested output frame with
   `s1Config L 0 1 (a+b+2) (2^b-1) 0 (h+3*b+5)`.
6. `outerLCIncPostludeTape_eq_marker1S0_m2`: restates that endpoint
   directly as
   `s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) (a+b+2) (2^b-1) 0 H`,
   the exact general positive-z S0 input interface used by the q4 work.
7. `outerLCInc_marker1S0_inputBounds`: proves automatically that
   `0 < a+b+2` and `2^b-1 < 2^(a+b+2)`, the S0 width/value bounds.

This is the exact source-level theorem needed by the root integration to
replace the nested postlude frame with the canonical marker-1 S1/S0
configuration. Unfolding that target gives
`s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) (a+b+2) (2^b-1) 0 H`,
which matches the **general positive-z S0 input family** in
`im-results/agent48-counted-inc0/Marker1TerminalQ4Macro.md`.

This is only an entry-configuration match, not a q4 closure. The exact
`107+12*(A+L)` prefix and the complete checkpoint/cycle/terminal law in that
document are for the fully checked **z=0 special case**. For positive z, the
first checkpoint times differ, the right checkpoint state is not yet reduced
to a general formula, and the first-cycle counted-drain law remains
conjectural. In particular, the authentic root has `z=2^b-1≥3`, so the
z=0 terminal theorem cannot be applied. The positive-z nested q4 macro (or
an alternative route to the z=0,b=0 family) remains a major open obligation.

**All declarations in the new endpoint module remain
uncompiled and unaccepted**: the local shell and Python runtimes in the
current invocation return tool-level `ClientError`, and no CI dispatch has
been made. A fresh local preflight, full dependency-chain compile, and
exported axiom audit are still required. The older 2,400-case simulator
remains computational evidence only.

## Positive-z first q4 checkpoint normal form

The direct simulator
`marker1_q4_checkpoint_sweep.js` extends the existing marker-1 S0
checkpoint experiment through z=9. The data and candidate decomposition
are recorded in `PositiveZCheckpointNormalForm.md`. Across z=0..9 for
A=4,L=2 and z=0..5 for A=3,L=2 / A=5,L=4, the first state-4/head-1
checkpoint has:
- left word `[0,1,1] ++ binDec(A+L+2, M-1) ++ LH`, with
  `M=2^A*(2^(L+2)-1)), independent of z;
- right suffix `0^3 1^(3*z+5) 0^2 1^(3*2^z) 0^4`, with no further ones;
- q4/read-0 event count `3*2^z+3*z+5`;
- first-checkpoint time matching
  `drainCost(z,0)+drainCost(2^z-1,0)+12*(A+L+z)+107`.

The exact intermediate S0 shapes are now identified computationally
in `PositiveZCheckpointNormalForm.md`: the initial drain output is
`s0Config ell0 A 0 z 0`, the second-drain input is
`s0Config ell1 z (2^z-1) 0 (3*z+5)`, and its output is
`s0Config ell1 z 0 (2^z-1) (3*z+5)`. Both drain stages match existing
`S0CountedDrain` theorem interfaces. The setup macro
(`12*(A+L)+3*z+97`) and final tail (`9*z+10`) are still unproved
transition macros; all observations remain computational, not formal.
This is separate from the later first-cycle drain at width
`2^z-1` described below.


## Positive-z counted-drain structural bridge

See `PositiveZFirstCycleDrainBridge.md`. The observed first-cycle cost
is arithmetically consistent with `s0Config_counted_drain_closed` at
all-ones width `K=2^z-1`, whose actual binary input value is
`2^K-1), plus a linear overhead `12*(2^z+z+6)+2`. This is a
parameterization hypothesis only: the q4 checkpoint's right nested counter
and exact transition decomposition remain open.

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


## Return/transfer postlude: finer exact decomposition

Let (h_1=h-(3a+m+5)), the B-state head after the already formalized
prelude plus outer binary H-run. The remaining source trajectory has the
following parameterized decomposition:

1. **Five-step marker exit:** from state B at (h_1+2), read four ones
   followed by zero. The state sequence is B/F/D/B/F/E and the head ends
   at (h_1+7).
2. **E scan:** scan (3a+m+3) consecutive ones from (h_1+7), ending
   in E at (h+5).
3. **Two-step zero boundary:** the E/0 and A/0 moves write ones at
   (h+5,h+6), ending in B at (h+7).
4. **Counted B/F/D sweep:** scan (b+1) triples of ones, exactly
   (3(b+1)) steps, ending in B at (h+3b+10). The per-triple output
   is (001) in increasing tape coordinates.
5. **Zero exit and fixed return:** B reads the zero at (h+3b+10),
   writes one and moves left to state C at (h+3b+9); then a fixed
   28-step trace ends in state D at (h+3b+5).

The cost identity is exact:
[
5+(3a+m+3)+2+3(b+1)+1+28=3a+42+m+3b.
]

The fixed tail is now isolated in
`OuterLCIncTail.lean`. Relative to its initial head (H+9), where
(H=h+3b), its finite input has ones exactly at offsets
({-3,0,1}). Its read/write window is ([-3,5]); the output is
state D at offset (-4), with ones at offsets
({-2,-1,0,3,4,5}). Crucially, offset (-4) is the final head cell
but is **not** read or written, so the frame theorem preserves it. This
is necessary: that cell is false when (b>0), but true when (b=0).

The output of the tail on offsets (-3) through (5) is
(011100111), exactly the target right word
`s0RightFacing 0 = [0,1,1,1,0,0] ++ d1pow 1`. The preceding (b)
left-facing d0 blocks are assembled from the first (b) B/F/D triples:
each target d0 block uses the preceding boundary one (the E-zero cell
for the first block, otherwise the previous triple's third cell) and
the next triple's first two zero cells. The final triple is consumed by
the fixed return tail.

The universal pointwise obligations in this historical decomposition
are now addressed by source-level candidates in
`OuterLCIncCanonicalEndpoint.lean`:
- the five-step bridge's four-one/zero input is extracted from the
  marker-frame output;
- the E-scan's `3a+5` one-run is aligned with the shifted unary block;
- the `b+1` B/F/D sweep is split by residues modulo 3 to identify the
  `d0pow b` prefix;
- the zero-valuation H-run is identified with `d1pow L ++ lh`;
- the fixed tail frame and both pointwise tape streams are composed into
  the marker-1 S1/S0 endpoint.

These are still **uncompiled source candidates**, not accepted universal
theorems. The immediate proof-engineering obligation is a local compile of
the full dependency closure and an exported `#print axioms` audit. The
subsequent mathematical obstacle is the positive-z q4 macro described
above, not the already-drafted nested-frame endpoint. The 2,400-case
simulator remains computational evidence only.
