# The \(A=1\) positive-\(z\) P1 endpoint is a Type-C checkpoint

**Status:** new source-level branch derivation from existing interfaces. No new Lean theorem has been compiled in this invocation; this is not a halt proof or a BB(6) result.

## Result

The final odd-width base case of the outer P1 encoding is not a failed P1 cycle. It is exactly the input family of the existing 46-step Type-C bridge.

Recall the outer encoding in FirstQ4P1Arithmetic:

\[
w(L,A)=A+L+1,\qquad
q(L,A)=2^{A-1}(2^{L+2}-1)-1.
\]

At the odd base case \(A=1\),

\[
w=L+2,\qquad q=2^{L+2}-2=2(2^{L+1}-1).
\]

The existing BinDec recurrence gives

\[
\begin{aligned}
\operatorname{binDec}(L+2,2^{L+2}-2)
 &= d_1 \mathbin{+\!\!+}
    \operatorname{binDec}(L+1,2^{L+1}-1)\\
 &=d_1 \mathbin{+\!\!+} d_0^{L+1}\\
 &=d_1 \mathbin{+\!\!+} d_0 \mathbin{+\!\!+} d_0^L.
\end{aligned}
\]

Here \(d_0^j\) denotes d0pow j. The last equality is the key base-case identity.

## Why the post-\(Q(z)\) checkpoint is Type-C

Let \(V\) be the state-4, head-1 tape produced by the existing
positiveZFirstCycle_from_checkpoint z w q theorem. Its left-facing stream is obtained directly from the endpoint in
PositiveZFirstCycleEndpoint.lean:

\[
\underbrace{011}_{\text{postlude frame}}
\;\Vert\;
\underbrace{111}_{\text{three surviving endpoint ones}}
\;\Vert\;
\operatorname{binDec}(w,q)
\;\Vert\; lh.
\]

Equivalently, for \(A=1\),

\[
V_{\rm left}
=
011\Vert d_1\Vert d_1\Vert d_0\Vert d_0^L\Vert lh.
\]

This is exactly the side word required by
typeC_input_from_sides in
PositiveZTypeCBridge.lean, with
tailL = d0pow L ++ lh.

The 13-cell Type-C window at head \(h=1\) is:

| Coordinates | Values | Source |
|---|---|---|
| \(h-10,h-9\) | \(0,0\) | first two bits of the \(d_0\) block |
| \(h-8,\ldots,h-1\) | eight \(1\)'s | the postlude's \(d_1\) plus the first \(d_1\) of binDec w q |
| \(h,h+1,h+2\) | \(0,0,0\) | fixed post-\(Q(z)\) frame |

The extra condition \(V(h+3)=0\), required by
typeCPrefix_from_checkpoint, is also supplied by that same frame.

This is the parity complement of the existing second-cycle 34-step prefix:
- when \(q\) is odd, binDec w q starts with \(d_0\), giving the two-zero guard used by secondCyclePrefix34;
- when \(q\) is even with \(q/2\) odd, it starts with \(d_1d_0\), giving the Type-C window above.

For \(A=1\), \(q=2^{L+2}-2\) is even and \(q/2=2^{L+1}-1\) is odd, so the Type-C case is forced.

## Existing continuation theorem that applies

The right-side scan hypotheses in
positiveZFirstCycle_then_secondCyclePrefix are independent of its
hqOdd hypothesis. The proof blocks for
hfirst, hsep0, hsep1, hblocks, and hzeros use the
same post-\(Q(z)\) right stream and the same parameters

\[
m=3\cdot 2^z+3z+7,\qquad n=2^{\,2^z-1}.
\]

They can therefore be reused unchanged. Replace only the 34-step local
prefix with:

typeC_to_state4 (46 steps), followed by
typeCPrefix_from_checkpoint.

The resulting source-level run has cost

\[
46+m+2+3n+29=m+3n+77,
\]

and ends at the same q4-tail frame
frameAt T3 g q4TailInside q4TailEnd.

Thus the P1 route has a natural \(A=1\) continuation; the odd base case
does not require inventing a new transition macro. It requires exposing
the post-\(Q(z)\) left-facing stream and replacing the q-odd second-cycle
guard with the Type-C input proof.

## Connection to the outer-width recurrence

firstQ4P1BinDec_iterated proves the encoder identity

\[
\operatorname{binDec}(w(L,A),q(L,A))
=d_0^{2k}\Vert
\operatorname{binDec}(w(L,A-2k),q(L,A-2k))
\]

whenever \(2k+1\le A\). For odd \(A\), the terminal residual parameter is
\(A-2k=1\). The identity above then gives the Type-C base word
\(d_1d_0d_0^L\).

This is an encoder/list recurrence, not yet a theorem that the machine
has physically consumed those \(2k\) blocks. That requires the q4-tail
frame-to-S0 identity and the corresponding postlude composition.

## Exact next obligations

1. Extract a public post-\(Q(z)\) side-profile lemma from the private
   cell calculations in
   PositiveZFirstCycleToSecondPrefix.lean. Its left side must be
   [false,true,true] ++ d1 ++ binDec w q ++ lh; its right side must
   retain the existing scan guards.
2. Prove the \(A=1\) BinDec identity above in the existing
   FirstQ4P1OuterWidthRecurrence.lean (the file already proves the
   \(A=1\) and \(A=2\) base expansions).
3. Compose that profile with typeC_input_from_sides and
   typeCPrefix_from_checkpoint.
4. Prove the q4-tail frame-to-S0 identity for this Type-C output, not
   merely for the second-cycle 34-step output.
5. Determine the remaining \(d_0^L\) tail's terminal continuation and
   connect it to the existing terminal SectionBits bridge.

The present note establishes the exact missing interface shape for
item 3. It does not discharge items 1, 4, or 5, and makes no claim that
the complete blank-root machine halts.
