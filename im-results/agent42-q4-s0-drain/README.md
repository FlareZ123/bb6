# Positive-z q4 first-cycle: arbitrary-left S0 drain factorization

Status: **computationally identified; source-level prefix/postlude proof open; generic S0 drain source module uncompiled**.

This is an intermediate research dossier, not a result suitable for `results/`.

## Exact candidate factorization

Let (z\ge 1) be the positive counter parameter in the marker-1 S0 family. Define

\[
a=2^z-1,\qquad N=2^a-1.
\]

At the first q4 checkpoint (j=1), the candidate prefix reaches a state-3 configuration with head

\[
h=3\cdot 2^z+3z+7
\]

and tape of the exact S0 form

\[
\operatorname{s0Config}(\ell,a,N,0,h),
\]

where \(\ell\) is the arbitrary residual left context. In head-facing order, the counter prefix is

\[
\operatorname{binDec}(a,N)=d0^{\,a}=(001)^a,
\]

and the right-facing suffix is exactly \(\operatorname{s0RightFacing}(0)\). The left tail after the counter is not assumed to be a canonical S1 word.

The proposed three phases are:

1. **Prefix from q4 checkpoint 1 to the S0 drain input**
   \[
   P(z)=3\cdot2^z+3z+58.
   \]
2. **All-ones counted drain**
   \[
   D(z)=\operatorname{drainCost}(N,0)
       =6\cdot4^a+42\cdot2^a-12a-48.
   \]
   Its exact target is \(\operatorname{s0Config}(\ell,a,0,N,h)\).
3. **Postlude to q4 checkpoint 2**
   \[
   Q(z)=9\cdot2^z+9z+16.
   \]

The short phases sum to

\[
P(z)+Q(z)=12\cdot2^z+12z+74
=12(2^z+z+6)+2.
\]

Consequently the first-cycle cost predicted by this factorization is

\[
C_1(z)=D(z)+12(2^z+z+6)+2.
\]

This is exactly the observed first-cycle cost law in the Agent 48 q4 dossier. The main advantage is structural: the large middle phase is the generic counted S0 drain, while the prefix and postlude are short source macros.

## Checked values

For the baseline (A=3,L=2), the first two q4 checkpoint times and the factorization are:

| (z) | (a=2^z-1) | (N=2^a-1) | (P(z)) | (D(z)) | (Q(z)) | (C_1(z)) | checkpoints |
|---:|---:|---:|---:|---:|---:|---:|---|
| 1 | 1 | 1 | 67 | 48 | 43 | 158 | 275, 433 |
| 2 | 3 | 7 | 76 | 636 | 70 | 782 | 503, 1,285 |
| 3 | 7 | 127 | 91 | 103,548 | 115 | 103,754 | 1,031, 104,785 |
| 4 | 15 | 32,767 | 118 | 6,443,826,972 | 196 | 6,443,827,286 | 2,627, 6,443,829,913 |

For (z=1), there is an earlier matching S0 configuration before checkpoint 1; the factorization uses the later one exactly (P(1)=67) steps after checkpoint 1.

The intermediate S0 input shape, drain endpoint tape, and postlude endpoint were checked with an independent exact TM2 simulator for (z=1,2,3). For (z=4), the prefix and intermediate S0 input shape were checked directly; the predicted counted-drain output tape was then used as the postlude's initial tape and the (Q(4)=196) postlude was simulated to checkpoint 2. Thus the (z=4) middle phase is not a 6.44-billion-step direct simulation; it is the part intended to be discharged by the generic drain theorem.

Additional parameter checks:

- (z=2): ((A,L)=(3,2),(4,2),(2,4)).
- (z=3): ((A,L)=(3,2),(4,2),(3,4)).
- (z=4): ((A,L)=(3,2),(4,2),(3,4)), with equal first-cycle cost and checkpoint times shifted by the outer parameter change.

These observations agree with the Agent 48 checkpoint table and its full-left-frame checker. They remain computational evidence, not a Lean proof of the q4 prefix or postlude.

## New source module

`S0CountedDrain.lean` attempts to prove the arbitrary-left-context source theorem:

\[
\operatorname{run}\;tm2\;(\operatorname{drainCost}(n,c))\;
  (\operatorname{s0Config}(\ell,a,n,c,h))
=
\operatorname{some}(\operatorname{s0Config}(\ell,a,0,c+n,h)).
\]

Its proposed proof generalizes the existing S1 all-valuation decrement:

- match the local carry input window using `binDec_carryPrefix` and `s0Config_left_cell`;
- use `carryPrefix_anyNonnegative_hRun` for the exact (15+12r) primitive prefix;
- prove the arbitrary-left output identity with `binDec_sub_one_carryPrefix`;
- compose the six-cell/right-run/left-output obligations through the existing `s0Config_counted_decrement_of_prefix`;
- obtain the complete drain by `countedIncs0).

The file currently exports:

- `s0Config_carryInput_match`
- `s0Config_decrement_leftOutput`
- `s0Config_counted_decrement_anyValuation_hRun`
- `s0Config_counted_decrement_inc0`
- `s0Config_counted_drain_general`
- `s0Config_counted_drain_closed`

**Validation status:** source-only; not yet compiled. The local container/Python execution tools failed in this invocation, so no claim of Lean acceptance or axiom-freedom is made. Agent 24 has been asked for one targeted local Lean 4.36.0-rc2 preflight of the exact import closure. CI should not substitute for that preflight.

## Remaining proof obligations

1. Prove the q4-checkpoint-1 prefix of length (P(z)) reaches the displayed arbitrary-left S0 configuration for all admissible (z,A,L).
2. Compile and audit the arbitrary-left S0 drain module, including `#print axioms` for every exported theorem.
3. Prove the q4-checkpoint-2 postlude of length (Q(z)) from the exact drain output.
4. Compose the three source theorems and compare the resulting q4 cycle theorem against the independent checkpoint simulator.
5. Keep the later-cycle conjectures separate; this dossier only addresses the first positive-z cycle.

No BB(6) value or global upper bound follows from this work yet.


## Later-cycle extrapolation: caution, not a theorem

A limited search also found arbitrary-left S0 all-ones drain inputs in later q4 cycles. For the conjectured width
\[
a_j=2(2^{z-1}-1)(2^{2^{j-1}}-1)+1,
\]
the exact local S0 input shape `d0pow a_j` on the left and `s0RightFacing 0` on the right was found for:

- ((z,j)=(2,2)): checkpoint time 1,285; S0 input at time 1,399, head 51, (a_2=7).
- ((z,j)=(3,2)): checkpoint time 104,785; S0 input at time 105,274, head 426, (a_2=19).
- ((z,j)=(2,3)): checkpoint time 105,095; S0 input at time 105,583, head 437, (a_3=31).

These are candidate counted-drain subruns, not proof of a full later-cycle factorization. In particular, the first-cycle postlude formula (Q=3h-5) **does not** extend naively: after constructing the predicted drain output for ((z,j)=(3,2)) and ((2,3)), (3h-5) steps do not reach the next q4 checkpoint. A 10-million-step postlude simulation for ((3,2)) still did not reach that checkpoint. The later-cycle postlude therefore has additional structure and must be investigated separately. Do not extrapolate the first-cycle (P,Q) formulas to later cycles without new evidence.




## Width audit correction from the second-cycle prefix bridge

Agent 48's source draft PositiveZSecondCyclePrefix.lean now gives the
second-checkpoint prefix with
m = 3*2^z+3*z+7 and n = 2^(2^z-1) three-one blocks. Its state-1
scan therefore produces n blocks, and the q4-tail frame leaves the
natural S0 counter block d0pow (n-1). At z=3 this is d0pow 127,
not d0pow 19.

This does not make the earlier observed d0pow 19 prefix false:
d0pow 127 = d0pow 19 ++ d0pow 108, and the S0 encoder permits an
arbitrary residual left context. Thus the same tape can be factored
as a width-19 S0 counter with d0pow 108 absorbed into the residual,
or as the width-127 block generated by the second-cycle prefix.
The parameter a is not a canonical width until a boundary/continuation
argument identifies which residual is intended.

**Correction to interpretation:** the earlier formula for a_j is only
an observed prefix factorization, not a proved or canonical later-cycle
counter width. In particular, it must not be used to infer a second
Q-postlude. The P2 bridge's natural generated width at (z,j)=(3,2)
is 127; the second-cycle Q macro and its local boundary remain open.
The previous observations are retained as tape-prefix data, not deleted.

## Root-to-first-q4 checkpoint source composition

\`FirstQ4CheckpointPostlude.lean\` now composes the final postlude of the
root's initial marker-1 S0 family with the existing first-three-phase
source draft in Agent 24's \`FirstQ4CheckpointPrePostlude.lean\`.

The post-drain S0 left-facing word begins
\`d1pow z ++ markerWord 2 ++ d0 ++ ...\`. Thus the q4/S0 postlude
\`q4S0Postlude_at\` applies with \`k=3*z+2\`: the first \`3*z+2\`
cells are ones, the right sentinel is zero, and the next four cells
are exactly \`0,1,0,0\`. The resulting theorem is:

- \`firstQ4Checkpoint_postlude\`: exact \`9*z+10\`-step run to the
  \`q4FrameAt\` finite frame;
- \`firstQ4Checkpoint_run\`: composition from
  \`s0Config (firstQ4Left0 L) A z 0 0\` to that first q4 frame, using
  the existing arbitrary-value drain, Rst1' macro, and all-ones drain.

**Status:** source draft only. The local Python/container execution
interfaces returned \`ClientError\` in this invocation, so neither this
new module nor its transitive closure has been compiled here. It remains
in \`im-results/\`; no Lean acceptance or axiom-freedom is claimed.
The remaining acceptance work is one ordered import-closure compile
through \`S0CountedDrain\`, \`Rst1PrimeBridge6Source\`,
\`FirstQ4CheckpointPrePostlude\`, \`Q4S0FirstCycleMacros\`, and
\`FirstQ4CheckpointPostlude\`, followed by the explicit q4 checkpoint
tape-shape identity.


## Positive-z Q(z) interface from canonical drained S0

PositiveZFirstCycleS0Input.lean packages Agent 48's
firstCycleQ_from_S0Input theorem directly for an S0 configuration.
It proves that if the residual left context has the exact prefix

    1^(3*z+7) ++ 0010 ++ tail

then after the all-ones S0 drain the tape has:

- a left-one run of length 3*(2^z-1)+3*z+7;
- the required zero sentinel immediately right of the head;
- absolute cells 0,1,2,3 = 0,0,1,0.

The wrapper firstCycleQ_from_drainedS0 therefore gives the exact
9*2^z+9*z+16-step Q(z) postlude on this canonical S0 family.

This is an interface lemma, not a proof that the still-open P(z)
prefix produces the required residual context. That remaining endpoint
identity must establish the displayed 1^(3*z+7) ++ 0010 prefix
from the q4-tail output. This file is also source-only and has not been
compiled in this invocation.


## Candidate second-cycle post-drain continuation

SecondCyclePostDrainBridge.lean contains two exact finite-trace source
drafts:

- state 3 on four zeros at head -3 to state 1 at head -1 (4 steps);
- state 1 on local pattern 001001 at head g to state 4 at head g+2
  (8 steps).

Combining these with the P2 output shape suggests the following
post-drain continuation. Put

- n = 2^(2^z-1),
- m = 3*2^z+3*z+7,
- H = m+2+3*n.

The P2 output has left counter d0^(n-1). If its residual left context
starts with 1^(m+8) followed by four zeros, then after the S0 drain the
left one-run has length

    K = 3*(n-1)+(m+8) = 3*n+m+5 = H+3.

A counted left sweep reaches head -3. The 4-step zero bridge enters
state 1 at -1. The sweep and right S0 suffix give a contiguous right
one-run from -1 through H+4, of length

    R = H+6 = 3*(n+2^z+z+5).

The state-1 three-one-block scan consumes R cells and ends at head
H+5. The 8-step 001001 bridge enters state 4 at H+7, the beginning
of the remaining right unary counter d1pow(2^(n-1)). A state-4 E-scan
of length 3*2^(n-1) would then reach state 4 at
H+7+3*2^(n-1).

The finite prefix before this E-scan has cost

    3*K + 4 + R + 8 = 12*n + 12*2^z + 12*z + 63.

**Status:** candidate composition only, not yet a proved theorem.
The critical missing premise is the exact P2 endpoint residual-left
prefix 1^(m+8) followed by four zeros, plus the corresponding right-run
and bridge-input identities. The two finite bridges themselves are
source drafts and have not been compiled in this invocation. Do not
treat the displayed continuation or cost as an established BB(6) bound.

## Exact first q4 checkpoint right tail

The complete right-facing tape at checkpoint (j=1), starting at cell 2 (head is at cell 1), has the observed run-length encoding

\[
0^3\;1^{3z+5}\;0^2\;1^{3\cdot2^z}\;0^4.
\]

This was checked for (z=1,2,3,4), and for the additional outer parameter choices ((A,L)=(4,2),(2,4),(3,4)) at (z=2) and ((4,2),(3,4)) at (z=3). The right tail is independent of (A,L) in these tests.

Together with the known left checkpoint frame
\[
011\;\Vert\;\operatorname{binDec}(A+L+2,M(A,L)-1)\;\Vert\;lh,
\]
this gives a concrete candidate input frame for a uniform source theorem proving the (P(z))-step prefix to the arbitrary-left S0 drain input. This is more useful than the earlier informal description of the positive-z right tail.


The postlude output at checkpoint (j=2) has the corresponding right-tail form

\[
0^3\;1^{h_1}\;0^2\;1^{3\cdot2^{a_1}}\;0^4,
\qquad
h_1=3\cdot2^z+3z+7,\quad a_1=2^z-1.
\]

This was checked by direct simulation for (z=1,2,3), and by the predicted-drain splice plus direct postlude simulation for (z=4). In particular, for (z=4) the final run lengths are (0^3,1^{67},0^2,1^{98,304},0^4). This supplies a concrete right-tail target for the first-cycle postlude theorem.


## Extended (z=5) structural test

For (A=3,L=2,z=5), the first q4 checkpoint occurs at step 8,003. The exact short phases were checked directly:

- (P(5)=169) reaches state 3 at head (h_1=118);
- the left prefix is (d0^{31}), the right suffix is exactly `s0RightFacing 0`, and there are no further nonblank cells to the right;
- the predicted drain output has a right unary interval of length (3\cdot2^{31}=6,442,450,944);
- simulating (Q(5)=349) steps from that predicted output reaches state 4 at head 1, with the exact checkpoint-2 left frame and right RLE
  \[
  0^3\;1^{118}\;0^2\;1^{6,442,450,944}\;0^4.
  \]

The corresponding middle cost and total first-cycle cost, **predicted by the drain formula rather than directly simulated**, are

\[
D(5)=27,670,116,200,758,640,220,
\]
\[
C_1(5)=27,670,116,200,758,640,738.
\]

This extends the short-phase and endpoint-splice checks through (z=5), without simulating the enormous middle drain.


## Residual left context at the S0 input

The arbitrary context \(\ell\) is not arbitrary in the q4 prefix's image: in every tested case it begins with a run of

\[
1^{3z+7}.
\]

This was observed for (z=1,2,3,4,5) and for the tested outer ((A,L)) variations. The remaining suffix of \(\ell\) carries the outer left-frame information and varies with (A,L). Thus, after the S0 counter block \(d0^a\), the tape has a contiguous leading run of ones of length (3z+7), followed by the encoded outer context. This is likely relevant to proving the postlude's exact left-frame update.


## Reproducer

`q4_s0_drain_splice_check.py` records the exact TM2 transition table and reproduces the checkpoint-1 right tail, (P(z))-step S0 input, and checkpoint-2 left/right frames. It directly simulates the middle drain for (z\le3); for (z\ge4) it uses a symbolic all-one interval for the theorem-predicted drain endpoint and simulates only the postlude. It also checks the residual-left-context leading run.

The script was authored in this invocation but could not be executed here because the local Python/container tools failed. Its output is therefore pending execution; the numerical observations in this dossier come from the separate exact JavaScript simulations described above.


## Prefix transition skeleton

A transition trace of the (P(z))-step prefix for (z=2,3,4,5) exhibits the same cost decomposition

\[
P(z)=22+(3z+5)+3\cdot2^z+31.
\]

The (3z+5) term is the straight state-4 sweep across the first unary run in the checkpoint-1 right tail. The (3\cdot2^z) term is the long sweep over the second run, whose length is exactly (3\cdot2^z). In that sweep the repeated control cycle is

\[
(3,1)\to(1,1)\to(5,1)\to(3,1),
\]

which consumes three consecutive ones, writes (100), and advances the head by three cells. Viewed from the final head, the written triple is (001=d0), exactly the block used by the S0 counter prefix. The remaining 22- and 31-step pieces are fixed setup/terminal traces in the tested runs.

This is an empirical proof guide, not yet a Lean run lemma. It suggests proving the prefix by composing a fixed 22-step setup, a unary state-4 sweep, a repeated three-cell (111\mapsto100) sweep, and a fixed 31-step terminal macro.


The Lean module's imports were minimized after review: it now imports `CountedSuffixOutput`, `CountedReset`, `CountedCarryPrefixHRun`, and `S1Encoder` directly. It no longer imports the higher-level `S1CountedDrain` / `S1CarryInc0` wrapper, since the S0 suffix composition and the H-run theorem are the only required interfaces. This reduces unnecessary dependency on the S1-specific source wrapper.


Substituting (a=2^z-1) into the drain cost and adding the prefix/postlude overhead simplifies the first-cycle cost to the compact closed form

\[
\boxed{C_1(z)=6\cdot4^{2^z-1}+42\cdot2^{2^z-1}+12z+38.}
\]

The linear (2^z) terms cancel exactly. This is the cleanest expression of the first-cycle step-count law; it remains a conditional source-level result until the generic S0 drain and q4 prefix/postlude are formally compiled and composed.


## Compatibility with the root endpoint

The root source chain currently reaches an S1 configuration with marker 2 after the middle-34 prefix, then applies `outerLCInc_full_run` to an `outerLCIncPostludeTape`. The remaining root-side gap is the pointwise equality of that postlude tape with the intended canonical marker-1 S0/S1 configuration. Therefore the q4 initial-family identification is a target interface, not yet a proved root endpoint.

The actual root length parameter is `tm63Length1`, and the repository proves `tm63Length1_even` in `im-results/agent42-outer-lcinc/TM63Length1Parity.lean`. Thus the intended root q4 family has even (L), but the marker-1 canonical endpoint equality remains an explicit unresolved dependency; even parity alone does not solve the (z>1) terminal cycles.

If that equality identifies the post-reset target as
`s1Config L 0 1 A (2^b-1) 0 h`, then by the S1 encoder definition and `binDec L 0 = d1pow L` it is exactly
`s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) A (2^b-1) 0 h`.
For (b\ge2), (z=2^b-1>0) and (z<2^A), so the positive-z q4 first-cycle hypotheses would apply.


I compared this full residual-context identity bit-for-bit against direct S0-input tape extraction for ten cases: ((A,L,z)=(3,2,1ldots5),(4,2,5),(3,4,5),(2,4,2),(4,2,3),(3,4,3)). Every extracted left tail had exactly the predicted length and bits. This directly validates the interface required by the postlude shift proof over a wider parameter sample.


## Reparameterizing checkpoint 1 as Agent 48's P1 input

The first q4 checkpoint side pair is
`L_1 = 011 ++ binDec(A+L+2,M-1) ++ lh` and
`R_1 = 000 ++ 1^(3z+5) ++ 00 ++ d1pow(2^z) ++ 0000`,
where `M=2^A*(2^(L+2)-1)`.  Agent 48's P1 input uses
`firstCycleCheckpointLeft w q = 011 ++ d0 ++ binDec(w,q) ++ lh`
and the same right side.

For every `A>0`, define
`w=A+L+1` and
`q=2^(A-1)*(2^(L+2)-1)-1`.  Then
`2*q+1=M-1`, `q<2^w`, and the source encoder's exact
`binDec_odd` identity gives
`binDec(A+L+2,M-1)=d0 ++ binDec(w,q)`.  Therefore the two
canonical side encodings are identical.  The source draft
`FirstQ4P1Reparam.lean` formalizes this arithmetic/list-level
reparameterization and proves equality of the side-based tapes.

**Important boundary:** this does not yet prove that the actual
`q4FrameAt` output of `firstQ4Checkpoint_run` equals the side-based
tape.  The remaining lemma is pointwise tape extensionality using
`s0LeftSweep_shift`, `q4FrameAt_tape`, and the S0 left/right cell
lookups.  Once that lemma is in place, the existing
`firstCyclePrefix_to_s0DrainInput` can be applied with the displayed
`(w,q)` without any new transition macro.  The authentic blank-root
endpoint equality remains a separate open obligation.


## Pointwise frame-to-side identity: exact coordinate target

`FirstQ4P1FrameCoordinates.md` records the cellwise derivation from
the actual `q4FrameAt` output of `firstQ4Checkpoint_run` to the
canonical side encoding. With `h=3*z+5` and `k=3*z+2`,
`s0LeftSweep_shift` gives a zero at cell 4, ones on cells 5 through
3*z+6, and the original S0 tape elsewhere; the final q4 frame writes
cells 0..3 as 1,0,0,0. The resulting left side is
`011 ++ binDec(A+L+2,M-1) ++ lh`; the right side is
`000 ++ 1^(3*z+5) ++ 00 ++ d1pow(2^z) ++ 0000`.
Combined with `FirstQ4P1Reparam.lean`, this gives the exact
pointwise lemma needed to identify the first q4 checkpoint with
Agent 48's P1 input. The coordinate derivation is source-level and
not yet Lean-compiled.


**Exact source-expression correction:** Agent 24's `firstQ4Left2` uses
`binDec (L+A+2) (2^(L+A+2)-2^A-1)`, not a literal `M-1`.
The updated `FirstQ4P1Reparam.lean` now proves
`2^A*(2^(L+2)-1)=2^(L+A+2)-2^A` and uses the exact source expression
in the left-side theorem. Thus the parameter bridge no longer relies
on an unproved notational identification.


## Isolated arithmetic preflight target

The arithmetic core has been split into
`FirstQ4P1Arithmetic.lean`, which imports only the source-exact
`Agent8S1Encoder`. It proves the exact source expression
`2^(L+A+2)-2^A-1 = 2*q+1`, the width bound `q<2^(A+L+1)`,
and the `binDec_odd` list rewrite. The larger
`FirstQ4P1Reparam.lean` now imports this isolated module and
Agent 48's P1 endpoint module only for the side-encoding adapter.
This separation permits a meaningful local Lean preflight of the
arithmetic theorem even if Agent 48's wider P1 import closure is still
being repaired.


The first Lean 4.36.0-rc2 isolated preflight exposed four proof-script
issues in this module (a namespace-qualified order lemma, a non-core
normalization tactic, a rewrite that altered both sides of the exponent
identity, and an exponent-associativity mismatch in the BinDec rewrite).
These have been repaired in the current source. The corrected arithmetic
module compiles in a local isolated harness using the verbatim source
slice needed here: `d0`, `d1`, `lh`, `d1pow`, `binaryCounterFuel`,
`binDec`, and the source `binDec_odd` theorem. The six exported axiom
profiles are all exactly `[propext, Quot.sound]`.

**Scope of this check:** the harness compiled the exact arithmetic
proof against that verbatim encoder slice; it did not compile the full
`S1Encoder.lean` / `ChampionRootBridge` import closure, nor
`FirstQ4P1FrameLeft.lean`. Do not report the complete source module or
the actual q4 frame-to-side bridge as accepted yet.


The side-based adapter now also composes directly with Agent 48's
existing `firstCyclePrefix_to_s0DrainInput`: for `A>0` and `1≤z`,
`firstQ4P1_sidePrefix_to_s0DrainInput` gives the exact S0 drain input
after `3*2^z+3*z+58` further TM2 steps. This is conditional on the
first q4 checkpoint's actual frame output having the side shape proved
in `FirstQ4P1FrameCoordinates.md`; that pointwise frame identity is
still the outstanding link.


## Full first-cycle composition from the side-based root checkpoint

The adapter now includes
`firstQ4P1_sideCycle_to_secondFrame`. It reuses Agent 48's complete
`positiveZFirstCycle_from_checkpoint` theorem, so the side-based root
checkpoint runs through the P1 prefix, the all-ones S0 drain, and Q(z)
to the next q4 frame with the exact source cost. No new transition
macro was introduced. This is still conditional on the pointwise
identification of the actual `firstQ4Checkpoint_run` output with the
side-based tape; the frame-coordinate note gives the exact remaining
lemma.


## Exterior blank-tail proof for the two-scan setup prefix

Added `PositiveZCheckpointSetupBlanks.lean`. It isolates the two
exterior assumptions still needed by Agent 48's setup composition:
`SetupPrefixLeftBlank` and `SetupPrefixRightBlank`. The initial S0
left-facing word has length `3*A+3*L+12`, so it is already blank
strictly left of `-(3*A+3*L+13)`; the right-facing word has length
`3*z+9), so it is blank strictly right of `3*z+9). Generic
`sweptLeft_preserves_before/after` lemmas show that the first left
sweep, B8, and second left sweep do not reach either exterior region.
The file proves both blank-tail predicates for the exact post-two-scan
tape at head `-(3*A+3*L+8)`.

This removes the exterior blank-tail obligations from the S0-specific
setup proof, conditional only on the exact initial S0 input and the
two-scan/B8 tape definition. The local suffix guards remain open.
The source draft is not yet Lean-compiled.


## First two setup-suffix guards from the two-scan prefix

Added `PositiveZCheckpointSetupFirstGuards.lean`. It proves the exact
`setupB20Input` nine-cell condition and the `rightOnes` premise for the
following `L+1` triples. The key identity is the exact `sweptLeft`
tape formula: after the second sweep, cell `h+1` is the cleared boundary
and every cell from `h+2` through `-(3*A+2)` is true. The B20 frame
does not touch cells at or beyond `h+4`, so the full L-sweep premise
follows. The local B20 left pattern comes directly from the final six
bits of the initial S0 left-facing word `lh=[1,1,0,1,1,1]`.

This discharges the first two fields (`b20` and `lRun`) of
Agent 48's `SetupSuffixGuards` for the exact two-scan tape. The
remaining five fields (B9 input, A+1 run, B6 input, z run, B30 input)
are still open. The source draft is not yet compiled.


## Complete SetupSuffixGuards source derivation

Added `PositiveZCheckpointSetupAllGuards.lean`. It derives the remaining
B9 input, A+1 run, B6 input, z run, and B30 input from the exact two-scan
prefix tape. Together with `PositiveZCheckpointSetupFirstGuards.lean`,
it constructs all seven fields of `SetupSuffixGuards` for `z>0).

The coordinate structure is:
- B9 reads the B8 marker and the first-sweep clear/one boundary after the
  L+1 right sweep;
- the A+1 run consists of the first sweep's remaining ones followed by
  the first three ones of the initial right S0 word;
- B6 reads the last cleared A-triple and the original cells 5–8;
- the z run is the tail of the initial `d1pow(z+1)` block;
- B30 reads the last z-triple, the extra final one, and the preserved
  blank right exterior.

This is a source-level proof draft only; it has not yet been Lean-compiled.
If it compiles, it removes the principal local-guard bottleneck from the
positive-z setup suffix. The actual two-scan run composition and final
encoder identity remain separate.
