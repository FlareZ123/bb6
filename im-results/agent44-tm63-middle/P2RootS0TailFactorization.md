# Root-specific factorization of the second q4Tail residual

**Status:** source-derived coordinate/arithmetic reduction; not Lean-compiled. This is an intermediate result, not a BB(6) halt proof.

## Why the generic P2 S0 composition applies to the authentic root

Use the existing notation:

- \(b = \text{middle34Result.right}\), with the root endpoint theorem giving \(b\ge 2\).
- \(A = \text{rootMarker1A} = \text{middle34Result.exponent}+b+2\), hence \(A\ge4\).
- \(z = \text{rootMarker1Z}=2^b-1\ge3\).
- \(L=\text{tm63Length1}\), \(w=\text{firstQ4P1Width}\ L\ A=A+L+1\).
- \(q=\text{firstQ4P1Value}\ L\ A=2^{A-1}(2^{L+2}-1)-1\).
- \(m=3\cdot2^z+3z+7\), \(n=2^{2^z-1}\), \(a=n-1\).
- The q4Tail output head is \(H=m+2+3n\).

The important root-specific strengthening is
\[
A\ge4\quad\Longrightarrow\quad q\equiv7\pmod8,
\]
because \(8\mid2^{A-1}\). In particular \(q\equiv3\pmod4\). Let \(r=q/4\). Then
\[
q=4r+3,\qquad r\equiv1\pmod2.
\]
The exact width is \(w=A+L+1\ge5\), and \(r<2^{w-2}\). Two applications of the source binDec_odd recurrence therefore give
\[
\operatorname{binDec}(w,q)
 = d0\; ++\; d0\; ++\;\operatorname{binDec}(w-2,r),
\qquad d0=[0,0,1].
\]
Since \(r\) is odd, the remainder itself begins with another d0:
\[
\operatorname{binDec}(w-2,r)
 = d0\; ++\;\operatorname{binDec}(w-3,\lfloor r/2\rfloor).
\]
The first identity is all that is needed for the immediate P2 endpoint; the second exposes a longer residual pattern for subsequent work.

## Exact residual list to use in p2ActualS0_to_state2

Set
\[
\text{tail} := [\text{true}]\; ++\;
  \operatorname{binDec}(w-2,r)\; ++\;\text{lh},
\]
and instantiate Agent 48's p2ActualResidualLeft m tail. Its left-facing word is
\[
d0^{a}\; ++\;
1^{m+2}\; ++\;0101\; ++\;1^7\; ++\;00\; ++\;
\bigl(1\; ++\;\operatorname{binDec}(w-2,r)\; ++\;\text{lh}\bigr).
\]
Thus the target canonical S0 configuration is
\[
\boxed{
\text{s0Config (p2ActualResidualLeft m tail) a (2^a-1) 0 H
}.
\]

The tail factorization is forced by the first-cycle endpoint source, not a guessed padding:
\[
\text{firstCycleResidualLeft z (replicate 4 true ++ binDec w q ++ lh)}
=1^{3z+7}\;0100\;1^4\;d0\;d0\;\operatorname{binDec}(w-2,r)\;\text{lh}.
\]
The first-cycle Q output leaves the four ones at cells \(-1,-2,-3,-4\), followed by the two d0 blocks. The second 34-step bridge changes the first d0 block's two leading zeroes to ones, while its third bit was already one. It also leaves the second d0 block untouched. Consequently the second q4Tail residual after its 0101 boundary is exactly \(1^7 00\) followed by the third bit of that second d0 block and the remaining BinDec word, i.e. the tail above.

## Coordinate checks for the S0 identity

Let \(h=1\) be the second-prefix input head, \(h_1=m+5\) the E-scan/two-zero setup head, \(h_2=m+7\), \(g=h_2+3n\), and \(H=g-5=m+2+3n\).

1. The left counter prefix is already covered by the generic lemma q4Tail_output_leftCounter: the q4Tail frame has left-facing prefix \(d0^{n-1}=d0^a\), using only \(T_2(h_2-1)=1\), supplied by the two-zero setup.
2. The residual begins at \(H-3a=m+5\). The E-scan plus the two-zero setup and the second 34-step frame give \(1^{m+2}\) at cells \(m+5,\ldots,4\).
3. The second 34-step frame gives cells \(3,2,1,0=0,1,0,1\).
4. At cells \(-1,\ldots,-7\), the first four ones come from the first-cycle residual, the two leading zeroes of its first d0 block are rewritten to one by the second 34-step frame, and the third bit of that d0 block was already one.
5. At cells \(-8,-9\), the first two bits of the second d0 block are zero. Its third bit at \(-10\) is the leading true in tail.
6. The q4Tail frame's right-facing nine-cell word relative to head \(H\) is
   \[
   0,1,1,1,0,0,1,1,1
   = \text{s0RightFacing 0}.
   \]
   Beyond those nine cells, the source right stream has been consumed through its d1^n blocks and has a blank tail (the four explicit terminal zeroes plus sideBit's zero padding).

These are exactly the left/right pointwise obligations needed for a config_ext proof identifying the q4Tail frame with the boxed S0 configuration. Then Agent 48's existing p2ActualS0_to_state2 composes the closed S0 drain, the corrected 73-step boundary bridge, and the right continuation.

## Expected root-level consequence

Once the frame-to-S0 identity is proved, it composes with Agent 38's tm63_blank_reaches_q4Tail and Agent 48's p2ActualS0_to_state2 to give an exact, source-level blank-root run through the second-cycle P2 continuation to state 2. The result would still be a finite-prefix theorem only; the subsequent state-2 trajectory and eventual halting remain open.

## Exact source dependencies

- im-results/agent44-tm63-middle/TM63RootMarker1Endpoint.lean: \(b\ge2\), root \(A,z\).
- im-results/agent42-q4-s0-drain/FirstQ4P1Arithmetic.lean: \(w,q\), binDec_odd.
- im-results/agent48-counted-inc0/PositiveZFirstCycleEndpoint.lean: firstCycleResidualLeft, firstCyclePrefixTailFrame_leftFacing, firstCyclePrefixTailFrame_rightFacing.
- im-results/agent24-champion-time/PositiveZFirstCycleToSecondPrefix.lean: exact second-prefix input window and first-cycle-to-second-prefix composition.
- im-results/agent48-counted-inc0/PositiveZSecondCyclePrefix.lean: q4Tail frame.
- im-results/agent48-counted-inc0/D0SweepLeftFacing.lean: q4Tail_output_leftCounter.
- im-results/agent48-counted-inc0/P2ActualBoundaryComposition.lean: p2ActualS0_to_state2.

No new Lean declaration is certified by this note. The local shell tool returned ClientError, so no local compilation was possible in this invocation.
