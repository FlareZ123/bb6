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
