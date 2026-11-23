# Positive-z q4 first-cycle: arbitrary-left S0 drain factorization

Status: **direct arbitrary-A q4Tail-to-terminal composition drafted from the authentic blank-root trajectory; external BusyCoq/Rocq TM63 halting proof exists for the same raw table; this Lean dependency closure and exact score witness remain uncompiled/unverified**.

This is an intermediate research dossier, not a result suitable for `results/`.

**External halting baseline.** The pinned BusyCoq/Rocq source at
ccz181078/busycoq@3f302b87f5fb933c46e97672ffbb6907f373fb6e,
verify/SOBCv5.v, defines the same literal TM63 table and proves
TM63.halt : halts tm c0 (the module begins at line 10748, `init` is
at line 11000, and `halt` is at lines 11249–11281). See
[CoqHaltItinerary.md](../agent42-champion-terminal/CoqHaltItinerary.md)
and [Agent 48's root/table bridge](../agent48-champion-root/README.md).
That external theorem establishes halting, but not an exact primitive
step count and is not imported into Lean here. This dossier's remaining
purpose is the counted source itinerary and exact score, not rediscovery
of the already-formalized halting fact.

**Recurrence proof status.** The moving-exponent inequalities used below
are separately kernel-checked in
[Agent 38's `TM63TowerRecurrence.lean`](../agent38-root-q4tail/TM63TowerRecurrence.lean),
whose `tower_recurrence_bounds` theorem was compiled locally with Lean
4.36.0-rc2 and has exported axioms `[propext, Classical.choice, Quot.sound]`
with no `sorryAx`. This certifies only the scalar recurrence inequalities;
it does not validate the TM63 source itinerary or the conditional score
bounds.


## Direct arbitrary-A q4Tail terminal path

The shortest current route does **not** iterate the P2 q4Tail-to-q4Tail
recurrence toward its `111111` residual. It sends the authentic second
q4Tail frame directly through the complete S1 dispatcher.

For the root instance, set
`L=tm63Length1=76`, `A=rootMarker1A>=2`, and
`z=rootMarker1Z>=3`. The general adapter uses

[
W=A+L+2,qquad M=2^A(2^{L+2}-1),qquad N=M-3.
]

Since (L) is even, (2^{L+2}equiv1pmod3), hence (3mid M) and
(3mid N). The full 24-class dispatcher therefore exits with marker
zero and produces the existing S1 reset configuration accepted by the
arbitrary-exterior terminal `SectionBits` theorem.

The authentic root draft supplies

[
operatorname{run};tm2;
(	exttt{rootToSecondQ4Cost}+	exttt{rootSecondQ4TailPrefixCost});
	exttt{blank}
=
operatorname{some}(
	exttt{shiftConfig rootMarker1Head rootSecondQ4TailFrame}).
]

The exact frame identity rewrites
`rootSecondQ4TailFrame` as
`q4TailS0Frame z (A+L+1) (firstQ4P1Value L A)`. The general terminal
suffix is transported to this translated frame by `shift_run`; the
final S1 configuration is re-expressed at the translated physical head
using `s0Config_shift`. The unrestricted terminal tape contract then
follows from `s0_reset_sectionBits`.

[`TM63GeneralQ4TerminalComposition.lean`](TM63GeneralQ4TerminalComposition.lean)
packages this join. Its intended exports are:

- `tm63_blank_reaches_general_q4_terminal`: the composed blank-root run
  to the marker-zero terminal S1 configuration;
- `tm63_general_q4_terminalSectionBits`: the terminal section contract
  at the translated physical head;
- `tm63_blank_halts`: the corresponding original-TM2 halt theorem;
- `tm63_blank_attainable`: the exact symbolic champion score witness.

The score expression is

[
S=C_{m root}+C_{m q4}+59+12(W+E)+7,
]

where (C_{m root}=	exttt{rootToSecondQ4Cost}+
	exttt{rootSecondQ4TailPrefixCost}),
(C_{m q4}=	exttt{q4TerminalPrefixCost};L;A;z), and
(E=(	exttt{q4TerminalResult};L;A;z).	exttt{exponent}).
The final (+7) is the existing six-step champion-root offset plus
the final undefined-query scoring correction. The q4 prefix cost includes
the counted drain and the complete `sectionResult` dispatcher cost.
The dispatcher also admits an exact three-increment state map and a closed 2-adic cost correction; see [`SectionResultThreeCycle.md`](SectionResultThreeCycle.md) for the recurrence and derivation. The 2026-11-20 algebraic refinement additionally proves `popcount(N)=A+L` for `N=2^A(2^(L+2)-1)-3` (`A≥2`) and collapses the conditional Attainable score to a single weighted sum over `b_0=R`, `b_{j+1}=2^b_j-1`, with explicit polynomial correction. This is an exact algebraic reduction, not a compiled root theorem; see the final sections of [`SectionResultThreeCycle.md`](SectionResultThreeCycle.md). A sharpened paper derivation isolates the final counted increment. For \(N=3k\ge3\), \(R\ge5\), and \(b_{j+1}=2^{b_j}-1\), the dispatcher-plus-terminal tail satisfies
\[
6(b_N+1)^2\le D_N\le
6b_N^2+60b_N+(6N^2+57N-66)b_{N-1}
+48N+90k^2+111k+12(N+1)U+90.
\]
Since \(b_{N-1}=\log_2(b_N+1)\), the remainder is \(o(b_N^2)\). A further paper-level root-prefix analysis gives the two-sided estimate
\[
6n^2+42n-12m-48\le C_{\rm root}
\le6n^2+821n+99\sqrt n+39m+1165<7n^2,
\]
where \(n=2^m\), \(m=2^z-1\), \(B\le z\le m/2\), and \(z\ge10\). The lower bound is the \(D_m\) summand; the upper bound is the explicit decomposition above. Hence \(C_{\rm root}=6n^2+O(n)\sim6n^2=o(R^2)\) for \(R=2^{n-1}-1\). The separate root drain is \(O(R^2)\), so the full conditional score has \(S_{\rm full}\sim6t_2(N,R)^2\) along this q4 parameter family. The exact score split \(S=C_{\rm root}+D_{\rm root}+D_N\), together
with the explicit root-prefix and dispatcher bounds, gives
\(S_{\rm TM1}<9b_N^2\). A coupled induction on the terminal-counter recurrence now gives a moving-exponent scale bound. For every \(j\ge2\),
\[
T_{j+3}^{T_{j+2}^{23/8}}<V_j,\qquad V_j^{T_{j+2}^{4092}}<T_{j+4}.
\]
With \(q=M+N+50\), \(b_N=V_{q-4}\), and the existing source-conditional score bracket \(6b_N^2<S_{\rm TM1}<9b_N^2\), this yields
\[
\boxed{6T_{q-1}^{2T_{q-2}^{23/8}}<S_{\rm TM1}<9T_q^{2/T_{q-2}^{4092}}.}
\]
This supersedes the earlier fixed-exponent estimate and strictly sharpens the adjacent-tetration bracket. The recurrence-only inequalities are now formalized in Agent 38's standalone Lean module; the score interpretation remains conditional on the uncompiled authentic-root and dispatcher composition. See [TM63PublishedTowerSandwich.md](TM63PublishedTowerSandwich.md) for the proof and [DirectTerminalTetrationBound.md](../agent24-champion-time/DirectTerminalTetrationBound.md) for the exact terminal lower bound. The consolidated note also proves \(q<T_{11}\), so
\(T_q<T_{T_{11}}\), below the published right endpoint.

**Evidence boundary:** this is a source-level integration candidate, not
an accepted halt or lower-bound result. Lean 4.36.0-rc2 is now installed
locally, and the isolated `SectionResultThreeCycleModel.lean` compiles
with warnings treated as errors. Its principal theorem axiom profiles
are exactly `[propext, Quot.sound]`. That file copies the recurrence
definitions into a separate namespace; it does not compile the original
`CostRecurrence.lean` import closure or prove that candidate dispatcher
cost equals the authentic TM2 primitive run length. The authentic
root-to-q4Tail chain, counted drain, complete original-source dispatcher,
and this composition remain uncompiled together. Critic's acceptance
gate still forbids substituting CI for local preflight. Keep this work
in `im-results/` until the original dependency closure compiles and its
exported axiom profiles are checked. It does not establish a global
six-state upper bound or exact BB(6).

## Machine-checked isolated dispatcher arithmetic model

'SectionResultThreeCycleModel.lean' is a standalone Lean 4.36.0-rc2
file. It copies 'v2', 'proposedIncrementCost', the marker/exponent/right
updates, and 'sectionResult' from
'../agent24-champion-time/CostRecurrence.lean' into an isolated namespace
so the recurrence can be checked without the repository-wide import
closure.

The file proves:

- 'sumV2_add_popCount': the exact binary valuation identity
  \(\sum_{r=1}^{N}v_2(r)=N-s_2(N)\);
- 'sectionResult_cost_three_cycle': for a marker-zero dispatcher with
  \(N=3k\), the exact cost is
  \(31N-12s_2(N)+\sum_i(6\cdot4^{b_i}+42\cdot2^{b_i}+12a_i-9b_i)\);
- 'sectionResult_one_dimensional_cost': after adding the terminal
  \(12E\), \(12(s_2(N)+2)\), and fixed 66 correction, the exact
  expression reduces to
  \(90k^2+111k+90+12(3k+1)U+\operatorname{oneDimSum}(3k,R)\),
  a sum depending only on the right-counter recurrence.
- 'popCount_q4_terminal_index': for \(A\ge2\),
  \(s_2(2^A(2^{L+2}-1)-3)=A+L\);
- 'q4_terminal_index_mod_three': even \(L\) makes the q4 terminal
  index divisible by three;
- 'sectionResult_q4_terminal_cost_even': the exact cost formula
  specialized to arbitrary \(A\ge2\) and even \(L\).

The source file's '#print axioms' checks report only
'[propext, Quot.sound]' for these principal theorems. Its SHA-256 is
'21af81f192d7b828274a7f89c888f740a3dee0bc365d99e09dcc1d8999a35ea8'.

**Scope boundary:** this is a machine-checked theorem about an isolated,
source-shaped copy of the recurrence. It does not import or compile the
original 'CostRecurrence.lean' closure, establish that its candidate
costs are authentic TM2 run lengths, or prove the blank-root halt/score
composition. The one-dimensional dispatcher-plus-terminal elimination is now
formalized for the stated correction terms. The three-step state map and
dominant-increment asymptotic remain algebraic derivations in the Markdown
note; the full root-prefix and counted-drain score composition is not
formalized by this file.

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

The preferred direct path has four acceptance requirements:

1. Compile the exact transitive closure of `TM63RootQ4Tail.lean`,
   `P2RootS0FrameIdentity.lean`, `GeneralQ4TailTerminalComposition.lean`,
   and `TM63GeneralQ4TerminalComposition.lean` with Lean 4.36.0-rc2. The direct terminal path uses the frame-only module; `P2RootS0Identity.lean` is needed only for the separate next-q4Tail recurrence.
2. Repair concrete elaboration failures, then inspect the exported
   `#print axioms` profiles for the root, dispatcher, terminal, halt, and
   attainable theorems. Reject `sorryAx` and unapproved oracles.
3. Only after successful local preflight, use the existing manual source
   acceptance target; do not create a new workflow or substitute CI for
   local compilation.
4. Evaluate or otherwise present the exact symbolic score clearly, and
   compare it with the published approximate halting-time analysis without
   confusing primitive steps with sigma score.

The arbitrary-left first-cycle S0 factorization above remains an alternate
route. If that route is needed, its separate obligations are to prove the
q4-checkpoint-1 prefix, compile and audit the generic S0 drain, prove the
q4-checkpoint-2 postlude, and compare the composed cycle theorem with the
independent simulator. Later-cycle extrapolations remain conjectural.

No BB(6) value or global upper bound follows from the current source drafts.


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

As of 2026-11-19, Agent 44 has added `im-results/agent44-tm63-middle/TM63RootMarker1Endpoint.lean`, a source-only composition of the blank-root middle-34 / SectionResult handoff with `outerLCIncPostludeTape_eq_marker1S0_m2`. Its intended theorem reaches state 3 at the exact postlude head with tape equal to the canonical marker-1 `s0Config` tape, so the q4 initial-family identification now exists as a root-composition draft rather than only a target interface. The upstream source was corrected to carry the actual T3 post-prelude tape and the `v2 n = r` witness (commits `86234f2`, `7753204`), and the root wrapper now retains T3 with (r=0) (commit `7392c13`). None of these corrections or the endpoint composition has yet been Lean-compiled or axiom-audited; exact local preflight is pending. The root-specific bound (b\ge2) (hence (z\ge3)) is now source-drafted in `TM63RootMarker1Endpoint.lean` as `tm63Middle34Result_right_ge_two` / `tm63Middle34Result_z_ge_three`; it remains uncompiled and must be included in the later endpoint acceptance target before invoking the positive-z q4 macro.

The actual root length parameter is `tm63Length1`, and the repository proves `tm63Length1_even` in `im-results/agent42-outer-lcinc/TM63Length1Parity.lean`. Thus the intended root q4 family has even (L), but the marker-1 canonical endpoint equality remains an explicit unresolved dependency; even parity alone does not solve the (z>1) terminal cycles.

The drafted equality identifies the post-reset target as
`s1Config L 0 1 A (2^b-1) 0 h`; by the S1 encoder definition and `binDec L 0 = d1pow L` this is exactly
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


## Generic q4Tail-to-S0 frame adapter

Added `Q4TailToS0Frame.lean`, a reusable exact frame-to-encoder theorem.
For (n\ge2), a source tape (T) at sweep head (h), and residual
left context (ell), it proves that the q4Tail output at head
(h+3n-5) is exactly

```lean
s0Config ell (n-1) (2^(n-1)-1) 0 (h+3*n-5)
```

under three explicit source-side hypotheses:

1. (T(h-1)=1), the left guard needed by the d0 sweep;
2. the untouched left ray from (h-2) is exactly `sideBit ell`;
3. the untouched right ray beginning at (h+3n+5) is blank.

The proof composes the existing `q4Tail_output_leftCounter` theorem
(which supplies the (d0^{n-1}) prefix), preservation of the left
exterior by the sweep/frame, and the q4Tail end frame. The nine cells
to the right of the S0 head are exactly
`s0RightFacing 0 = 011100111`; the third hypothesis supplies the
blank ray beyond them. A local encoder lemma establishes
`binDec (n-1) (2^(n-1)-1) = d0pow (n-1)`.

**Scope:** this is a generic conditional conversion, not yet the
authentic root instance. The remaining P2 work is to prove the exact
left-ray hypothesis with the corrected `1^(m+2) ++ 0100 ++ tail`
boundary (whose tail begins `100`) and the far-right blank ray from
the consumed `d1pow n) stream. The theorem is source-only and has
not been Lean-compiled in this invocation: local container and Python
execution both returned tool-level `ClientError`. No CI substitute
was dispatched, and no acceptance or axiom-freedom claim is made.


## Conditional q4Tail recurrence step

Added `Q4TailToNextQ4Tail.lean`. It composes the generic frame adapter
above with `p2S0_to_next_q4Tail` from
`P2S0ToNextQ4Tail.lean`. Under the same left-guard, complete residual
left-ray, and blank right-ray hypotheses, plus the authentic head
alignment (h=m+7) and the tail guard (100), it proves one complete
run from the current q4Tail frame through the corrected S0 drain and
q4/S0 postlude to the next q4Tail frame.

The composed run cost is the existing closed expression

```
(6*4^(n-1)+42*2^(n-1)-12*(n-1)-48)
+ (3*(m+2+3*n)-5)
+ (22+(m+2+3*n)+2+3*(2^(n-1))+29)
```

which the downstream cost theorem simplifies to
`6*4^(n-1)+45*2^(n-1)+4*m+20`.

This is the first generic q4Tail-to-q4Tail recurrence composition in
this directory. It still does **not** prove the source-specific P2
residual/blank-ray hypotheses or instantiate a blank-root run. Both
new Lean files remain source-only and uncompiled in this invocation;
the local runtime tools returned tool-level errors, and no CI
substitute was dispatched.


## Alternative P2 q4Tail recurrence route

This is the longer q4Tail-to-q4Tail continuation route. It is not required by the direct arbitrary-A terminal path above, but is retained as a fallback and as a reusable recurrence interface.


Agent 24's coordinate derivation is now recorded in
`im-results/agent24-champion-time/P2Q4TailToS0Identity.md`. It gives
the exact instantiation of the generic adapter for the q-odd second
prefix:

- (a=2^z-1), (n=2^a), (m=3\cdot2^z+3z+7);
- (h=m+7), (g=h+3n), (H=g-5=m+2+3n);
- (tail0=1^4\Vert binDec(w,q)\Vert lh);
- (tail1=100111\Vert tail0.drop(6));
- (ell=1^{m+2}\Vert0100\Vert tail1).

The three generic adapter hypotheses now have an explicit coordinate
proof target:

1. (T2(h-1)=1) follows immediately from the two-zero setup.
2. (T2(h-2-i)=sideBit(ell,i)) for every (i): the residual cells
   partition into the setup/E-scan/frame ones, the exact (0100)
   boundary, the (100111) six-cell tail prefix, and the untouched
   original S0 tape from cell (-7) leftward. The remaining source
   list is exactly (tail0.drop(6)); no far-left blank-tail assumption
   is needed.
3. (T2(g+5+i)=0) for every (i): the source right index is
   (3n+11+i), beyond the (6+3n)-cell word
   (s0RightFacing(n-1)), and all preceding operations preserve this
   ray.

With these three facts, `q4Tail_frame_eq_s0Config` applies with
`ell = p2ResidualLeft m tail1`. Since `tail1` begins `100`, the
corrected P2 S0 drain/postlude and Agent 48's next-prefix theorem apply.
The new `Q4TailToNextQ4Tail.lean` packages that composition: one
q4Tail-to-q4Tail recurrence step, with
`m' = H = m+2+3*n` and `n' = 2^(n-1)`, at cost
`6*4^(n-1)+45*2^(n-1)+4*m+20`.

This is a source-level coordinate derivation plus a conditional Lean
composition, not yet a compiled root theorem. The remaining decisive
work is to formalize Agent 24's three pointwise obligations against
the generic adapter and compile the exact dependency closure. The
A=1 Type-C branch may reuse the same adapter if it establishes the
same residual and blank-ray interface.

## Marker-2 zero-residue counted increment: finite replay (2026-11-20)

Added `m2_zero_residue_replay.py`, a standalone deterministic simulator
using the original TM2 table and the same S1 tape encoding as
`S1Encoder.lean`. It checks the full marker-2 source increment at
`n=8q), including the proposed primitive-step count and exact complete
endpoint tape.

The bounded test covers `q=1..32`, `a=1..4`, and `b=0..4), with
the minimal admissible width `L=(8q).bit_length()`: **640 parameter
cases and 481,424 simulated transitions passed**. This complements the
existing M0-even 8q replay and the separate M2 residue-four replay.

This is finite computational corroboration only. It does not prove the
all-q Lean theorem, replace local Lean 4.36.0-rc2 preflight, or establish
the authentic blank-root composition. The M2 zero-residue source closure
and complete dispatcher remain uncompiled and unaudited.

## Full 24-class section replay (2026-11-20)

Added `section_result_24_cycle_replay.py`, which reuses the same standalone
TM2 simulator and S1 tape encoder as the M2 zero-residue replay. It executes
the actual machine for 24 or 48 consecutive source increments and compares
the complete resulting configuration with the independently accumulated
`sectionResult` recurrence, including the exact primitive-step total and
head displacement.

All runs use admissible outer widths L>=4. The full-cycle portion covers 36
combinations of cycle length (24 or 48), initial marker (0, 1, 2), inner
width (1, 2, 3), and right counter (0, 1).
Every full-cycle run visits all 24 pairs `(marker, n mod 8)`. A further 12
short-prefix cases test growing right counters (2 -> 3 -> 7 -> 127 and
3 -> 7 -> 127), across all markers and inner widths 1 and 2. All complete
endpoint comparisons pass, covering **2,078,394 simulated transitions**.

This is still finite computational corroboration, not a proof of
`sectionResult_run_complete`. The universal source theorem and the authentic
blank-root composition still require Lean 4.36.0-rc2 compilation.

A final 27-case terminal-finish check is also included in the same script:
for L=4..6, a=1..3, b=0..2, it verifies that
`terminalMoves=59+12*(L+a)` leaves the machine live in state 0 at head h+7
reading 1, and that the next undefined query halts. This checks the exact
successful-move/final-query convention used by the +7 attainable-score
adapter. It adds 3,888 attempts (3,861 successful moves plus 27 undefined final
queries), bringing the combined suite to **75 cases, 2,082,255 successful
moves, and 2,082,282 total attempts**. This remains finite replay evidence,
not a proof.

## Execution note

The reported replay counts above were produced by executing equivalent
JavaScript/V8 simulations in this invocation, using the same TM2 transition
table, S1 tape encoding, cost formulas, and endpoint checks. The committed
Python files are intended as standalone reproduction artifacts, but the
Python runtime returned ClientError here, so those Python files themselves
were **not executed** in this invocation. Their syntax and reproduced output
still require a local Python run. This limitation does not change what the
V8 simulations executed, but it must be kept distinct from a successful run
of the committed Python artifacts.

## Published tower interval refinement

[TM63PublishedTowerSandwich.md](TM63PublishedTowerSandwich.md) now derives the source-conditional scale estimate
\[
6T_{q-1}^{2T_{q-2}^{23/8}}<S_{\rm TM1}<9T_q^{2/T_{q-2}^{4092}},
\qquad q=M+N+50.
\]
This is substantially sharper than the earlier adjacent-tetration bracket and the published interval. Agent 24 independently reviewed the moving-exponent induction and found no gap in its integrality, base cases, induction steps, or q-4 substitution. Agent 38 subsequently formalized the recurrence-only inequalities in `TM63TowerRecurrence.lean`, locally compiled under Lean 4.36.0-rc2 with only `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. The result remains intermediate until the authentic Lean composition passes local compilation and its transitive axiom audit; it is not a universal BB(6) upper bound.

## Arbitrary-depth iterated-log expansion and tight score bracket

The exact score admits an expansion to any fixed depth. Put
\(u_r=b_{N-r}\), so \(u_0=b_N\), \(u_1=\ell\), and
\(u_{r-1}=2^{u_r}-1\). For every \(1\le p\le N\),
\[
\begin{aligned}
S_{\rm TM1}
={}&\sum_{r=1}^{p}
\left(6(u_{r-1}+1)^2+42(u_{r-1}+1)+(12r-9)u_r\right)+E_p,\\
&0\le E_p<45u_p^2.
\end{aligned}
\]
The uniform tail is \(E_p<45u_p^2\) at every depth; the direct one-term bound improves this to \(E_1<13u_1^2/2\). The p=2 split isolates only the final two dispatcher summands. The terminal macro, final counted halt transition, +7 correction, raw initial drain, and root prefix remain in the non-summand tail, so they are counted exactly once. The authentic source indices are \(b_N=V_{M+N+46}\),
\(\ell=b_{N-1}=V_{M+N+45}\), and \(q=M+N+50\), with
\(A=\sum_{j=7}^{M+42}V_j+(5M+176)/3\). The proof establishes
\(N<R\) from this full \(A\), then uses geometric decay of the earlier
quadratic dispatcher costs and the root/polynomial bounds. The \(p=2\)
specialization is
\[
S_{\rm TM1}
=6b_N^2+54b_N+6\ell^2+57\ell+96
+15\log_2(\ell+1)+\Delta_2,
\quad 0\le\Delta_2<45\kappa^2.
\]
It also yields the especially tight additive interval
\[
6(b_N+1)^2+42b_N
<S_{\rm TM1}
<6(b_N+1)^2+42b_N+\frac{63}{10}\sqrt{b_N+1}.
\]
These are paper-level consequences of the conditional source-cost
identity, not Lean acceptance or an authentic-root halt theorem. See
[TM63ScoreAsymptotic.md](TM63ScoreAsymptotic.md) for the full
iterated-log and additive-bound derivations.

## 2026-11-23 exact RC2 closure status

The local Lean 4.36.0-rc2 bootstrap was attempted again in this continuation,
but the container shell returned a tool-level `ClientError` before producing
any command output. The split archive parts are present; the prescribed
local extraction and compiler preflight therefore remain unperformed.

Two existing `root-q4tail` manual-workflow runs were used as bounded
diagnostics after substantive source repairs:

- Run `45231291371` (head `a1a6226addb66d718cbfa691763b5767a6bf03be`)
  advanced past the repaired `M0EvenFourQ4Prefix` source and exposed
  remaining errors in `M0EvenEightQ4Prefix`,
  `M0EvenEightValuationFixedPrefix`, and `OuterLCIncFiveStep`.
- Run `45232595807` (head `75575d3...`) advanced further and exposed
  frame/head-contract and namespace issues in
  `M0EvenEightValuationFixedPrefix`, `M0EvenFourteenQ4Bridge`,
  `M2EvenResidueZeroFrames`, and `OuterLCIncTail`.

These runs are diagnostics only, not acceptance. The following source
repairs were made after or in response to those logs:

- `M0EvenFourQ4Prefix.lean`: imported the actual q4 suffix interface;
  normalized the modulo-three branch; made the finite prefix index
  explicit; corrected the bridge endpoint orientation; exposed the exact
  sweep endpoint; and normalized the left-prefix lengths.
- `M0EvenEightQ4Bridge.lean` and `M0EvenEightQ4Prefix.lean`: exported
  the source-left-facing theorem, aligned the finite-head predicate with
  `bridgeAt`, imported the q4 suffix interface, and made the counted
  sweep endpoint use the exact configuration shape.
- `M0EvenEightValuationFixedPrefix.lean`: corrected the finite marked-list
  order for the preserved `-14` bit, aligned the frame/head-check
  contracts, and made the zero-exit trace use explicit `Fin 6` states.
- `M2EvenResidueZeroFrames.lean`: exposed the required `leftOnes`
  namespace, normalized both frame coordinates, identified the setup frame
  with `config_ext`, rewrote `frameAt` forward to its explicit configuration,
  and normalized the counted-run input/output heads.
- `OuterLCIncFiveStep.lean`, `OuterLCIncTail.lean`, and
  `M0EvenFourteenQ4Bridge.lean`: imported/opened the actual
  `Agent48Champion` machine interface rather than relying on implicit
  names.
- `OuterLCIncPrelude.lean`: replaced the brittle right-zero boundary
  rewrite with an explicit inside-window and output-cell proof.

The latest source state includes these repairs but has **not** been
compiled after them. No further CI run was dispatched: the local preflight
gate remains unsatisfied, and CI must not be treated as a substitute.
The root-to-second-q4Tail theorem, `P2RootS0FrameIdentity`, the
arbitrary-`A` dispatcher/terminal composition, and their transitive
axiom profiles remain unaccepted. The source theorem
`tm63_blank_halts` in `TM63GeneralQ4TerminalComposition.lean` is still
a conditional draft, not a verified halt theorem. No exact BB(6) value or
global six-state upper bound follows from this work.
