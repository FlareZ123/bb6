# Positive-z q4 outer-counter descent

**Status:** intermediate arithmetic interface. The list identities below are Lean-proved in the current source draft and locally preflighted against a faithful extract of the encoder declarations they use. They do **not** prove that the Turing machine performs the corresponding deletions, do not close the q4Tail-to-S0 tape identity, and do not establish halting or a BB(6) score.

## Counter and encoded tail

For fixed L,A, define

\[
w(L,A)=A+L+1,\qquad
q(L,A)=2^{A-1}(2^{L+2}-1)-1,
\]

and the P2 source tail

\[
T_0(L,A)=1^4\;\Vert\;\operatorname{binDec}(w(L,A),q(L,A))\;\Vert\;lh.
\]

The encoder uses d0 = [0,0,1].

The Lean source is FirstQ4P1OuterWidthRecurrence.lean in im-results/agent42-q4-s0-drain. It proves:

1. For A ≥ 3,
   \[
   q(L,A)=4q(L,A-2)+3,
   \]
   and
   \[
   \operatorname{binDec}(w(L,A),q(L,A))
   =d_0\Vert d_0\Vert
     \operatorname{binDec}(w(L,A-2),q(L,A-2)).
   \]
   Here w(L,A)-2 = w(L,A-2).

2. Iterating the identity, for 2k+1 ≤ A,
   \[
   \operatorname{binDec}(w(L,A),q(L,A))
   =d_0^{\,2k}\Vert
     \operatorname{binDec}(w(L,A-2k),q(L,A-2k)),
   \]
   where d0^(2k) means the concatenation of 2k three-bit d0-blocks (Lean's d0pow (2*k)).

3. The exported tail lemma firstQ4P1Tail0_dropSixPlusSixK states that, whenever 2k+3 ≤ A,
   \[
   T_0(L,A).\operatorname{drop}(6+6k)
   =[1,0,0,1]\Vert
     \operatorname{binDec}(w(L,A-2(k+1)),q(L,A-2(k+1)))
     \Vert lh.
   \]

Thus at every zero-indexed cycle boundary k for which a further two-block reduction is available, the next tail begins with the P2 guard 100; the fourth bit is the final 1 of the second d0-block, and the remaining word is the lower-A counter. The offset 6+6k is four fixed setup ones plus 6k cells, i.e. 2k complete d0-blocks.

The number of guard-bearing boundaries is
\[
K=\left\lfloor\frac{A-1}{2}\right\rfloor,
\qquad A-2K\in\{1,2\}.
\]
This is a finite arithmetic descent: after K two-block reductions, the residual outer parameter is 1 or 2, so no further two-d0-block recurrence applies. It does not by itself prove that the machine reaches those boundaries.

## Connection to the current q4Tail programme

- The authentic root endpoint uses L = tm63Length1 = 76 and A = rootMarker1A. The source-level root bound tm63Middle34Result_right_ge_two gives A ≥ 4, since A = middle34Result.exponent + middle34Result.right + 2. The root-specific endpoint modules remain part of the uncompiled source chain.
- P2S0ToNextQ4Tail.lean already has a conditional theorem p2S0_to_next_q4Tail: given an S0 configuration whose residual tail begins with 100, it proves the S0 drain/postlude and next type-A q4Tail prefix. Its parameter update is H=m+2+3n, nNext=2^(n-1), with cost 6*4^(n-1)+45*2^(n-1)+4m+20.
- The missing composition is still the exact q4Tail-frame = S0-configuration identity, including the left d0pow counter and the right s0RightFacing 0 stream, plus a proof that successive q4Tail steps expose exactly the successive six-cell suffixes of T0. Agent38's P2ResidualBoundaryAudit.md gives the coordinate-level residual 1^(m+2) ++ 0100 ++ tail with tail beginning 100, but explicitly does not prove the full tape identity.
- After the outer parameter reaches 1 or 2, a positive-z terminal theorem is still required. The existing z=0 terminal macro does not automatically apply to the authentic root, whose positive-z branch has z ≥ 3.


## A=2 terminal boundary: z=1 diagnostic

The A=2 residual is now tested separately from the guard-bearing
\(A\mapsto A-2\) recurrence. The reproducible sparse-tape replay in
[A2TerminalBaseCaseZ1.md](A2TerminalBaseCaseZ1.md) starts from the exact
\(z=1\) S0 adapter input and reaches the existing SectionBits shape for
\(L=2,4,6\). The observed terminal parameters are
\(L_{\rm term}=L+4\) and
\(a_{\rm term}=(2^{L+7}-35)/3\); the measured prefix costs are
63,042, 1,040,298, and 16,745,874 moves respectively.

The decisive boundary is the state-4/head-1 local window \(11110000\).
After the A=2 residual is shifted, the remaining tail begins
\(1\Vert d_1\Vert d_0^{L+1}\), not the P2 guard \(100\). Thus the
guard-bearing recurrence cannot simply be continued through A=2. A
separate terminal macro is required. This diagnostic is only for \(z=1\)
(where \(n=2\) is a fixed point of \(n\mapsto2^{n-1}\)); the authentic
root has \(z\ge3\), so the uniform positive-z A=2 case remains open.

## Validation and limitations

The original recurrence draft used norm_num, but its actual import chain (Frontier → Symmetry → RootShift → ChampionRootBridge → S1Encoder) does not import Mathlib. The source was repaired with the kernel-decidable equality (2:Nat)^2=4 and Nat.mul_comm.

Lean 4.36.0-rc2 locally compiled the exact arithmetic and recurrence source against a faithful minimal extract of the encoder declarations they use (d0, d1pow, d0pow, binDec, and binDec_odd). The new tail theorem's axiom profile is [propext, Quot.sound], with no sorryAx. The full repository import closure and CI acceptance for this updated module remain outstanding; this local check must not be represented as a full-closure compile.
