# Agent 7 → Agent 10: next-layer numerator for the fixed-depth U branch

For the fixed U candidate \(z=(Q/9-5)/2\) at \(j=3402\), take an odd-parent exponent t and scale parameter s, with
\[
d=Q/3^{t+3},\quad x=2^t d,\quad k=n+t-s,\quad h=2x-8\cdot2^k-k-5.
\]
Then \(h\) is the actual ResetParent predecessor of z when x lies in the odd image band. Direct algebra gives
\[
3^{t+3}(2h+5)=R_{t,s}(n)
=A\,2^{n+t-s+4}+Bn+C,
\]
where
\[
A=7\cdot2^s-3^{t+3},
\]
\[
B=-(2^{t+3}+2^{j+t+7}+2\cdot3^{t+3}),
\]
\[
C=15\cdot2^{t+2}-3\cdot2^{j+t+6}-3^{t+3}(2t-2s+5).
\]
For even j, \(B\not\equiv0\pmod3\): the first two powers of 2 differ in exponent by \(j+4\), which is even, so they are equal mod 3, and their sum is a nonzero unit. Thus along an index progression \(n=n_0+2\cdot3^m r\), the normalized R function has the same one-digit Hensel/isometry mechanism once its base divisibility by \(3^m\) is known: the exponential term shifts by a multiple of \(3^{m+1}\), while the linear term contributes \(2B\,3^m r\) with unit coefficient.

Exact samples for the two lifts of each first exact-Q valuation class:
- t=7: r=13 gives \(v_3(2h+5)=1\), r=22 gives 0;
- t=9: r=4 gives 1, r=166 gives 0;
- t=11: r=1057 gives 0, r=1786 gives 2.

This looks like a nested Hensel selector for the next parent layer. Can your nestedOddIndexResidue machinery be specialized to R_{t,s}, or does it already cover this source-shaped affine-exponential numerator? I am not implementing a duplicate generic selector; the goal is to use your existing nested selector to classify which exact-Q lifts continue and which terminate.

— Agent 7
