# Full root-specific BinDec shape after the second q4Tail boundary

This sharpens P2RootS0TailFactorization.md. It is an arithmetic derivation from the root parameters, not a compiled Lean theorem.

Let
\[
A=\text{rootMarker1A}\ge4,\quad L=\text{tm63Length1},\quad
w=A+L+1,
\]
and
\[
q=2^{A-1}(2^{L+2}-1)-1.
\]
Then
\[
q=2^w-2^{A-1}-1.
\]
In its \(w\)-bit binary expansion, the low \(A-1\) bits are all one, bit \(A-1\) is zero, and the high \(L+1\) bits are all one. Since binDec emits \(d0=[0,0,1]\) for a one bit and \(d1=[1,1,1]\) for a zero bit, read least-significant bit first, the entire encoded word is
\[
\boxed{\operatorname{binDec}(w,q)
 = d0^{A-1}\; ++\; d1\; ++\; d0^{L+1}.}
\]
This is stronger than the two-leading-block factorization used for the immediate P2 boundary.

Writing \(r=q/4\), the two low one bits are removed. Hence
\[
\boxed{\operatorname{binDec}(w-2,r)
 = d0^{A-3}\; ++\; d1\; ++\; d0^{L+1}.}
\]
Therefore the exact root tail from the prior note has the completely explicit form
\[
\boxed{\text{tail}
 = [\text{true}]\; ++\; d0^{A-3}\; ++\; d1\; ++\; d0^{L+1}\; ++\;\text{lh}.}
\]
Here \(d0^k\) and \(d1^k\) mean \(k\) concatenated three-cell blocks, not bitwise powers.

The congruence hierarchy is immediate:
\[
q\equiv -1\pmod{2^j}\quad\text{for every }j\le A-1.
\]
In particular \(q\equiv7\pmod8\), and \(q/4\) has at least \(A-3\) low one bits. This gives the full repeated-d0 prefix in the second-cycle residual, not just one additional block.

## Why this matters

The second q4Tail-to-S0 identity can now be stated without an opaque BinDec tail:
\[
\text{tail}
=[1]\; ++\;d0^{A-3}\; ++\;d1\; ++\;d0^{L+1}\; ++\;[1,1,0,1,1,1].
\]
This may be the right interface for the next state-2/3 phase: after the explicit \(1^{m+2}0101\,1^7\,00\) boundary, the remaining source word is a finite run of d0 blocks, one d1 block, another run of d0 blocks, and the six-bit history marker. It is now possible to formulate a counted transition directly over these block counts rather than carry an opaque list parameter.

A proof can be built by repeated binDec_odd for the first \(A-1\) low one bits, one binDec_even at bit \(A-1\), then repeated binDec_odd for the high \(L+1\) one bits. The same argument at width \(w-2\) gives the tail factorization.

## Source dependency

im-results/agent42-q4-s0-drain/FirstQ4P1Arithmetic.lean defines the exact \(w,q\) formula and the binDec_odd/binDec_even recurrences. The root inequality \(A\ge4\) follows from rootMarker1A = middle34Result.exponent + middle34Result.right + 2 and middle34Result.right_ge_two.
