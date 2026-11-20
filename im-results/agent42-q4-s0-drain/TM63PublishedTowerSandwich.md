# TM63 exact recurrence: a source-conditional published tower sandwich

**Status:** intermediate mathematical derivation. Every statement about the actual TM1 run is conditional on the authentic blank-root/source-composition chain in **TM63GeneralQ4TerminalComposition.lean**. This note does not certify that uncompiled Lean composition and does not give a universal BB(6) upper bound.

## Setup

Use the tetration sequence
\[
T_1=2,\qquad T_{r+1}=2^{T_r}.
\]
Let
\[
V_0=63,\qquad V_{j+1}=2^{V_j}-1.
\]
Then, by induction,
\[
T_{j+3}+1\le V_j<T_{j+4}. \tag{1}
\]
The exact source-recurrence parameters from
[DirectTerminalTetrationBound.md](../agent24-champion-time/DirectTerminalTetrationBound.md)
are
\[
\begin{aligned}
A_0&=18+\sum_{j=0}^{6}V_j,\\
M&=31\,2^{A_0}-36,\\
B&=V_{M+42},\\
A&=V_7+\sum_{j=8}^{M+42}V_j+\frac{5M+176}{3},\\
N&=(2^{78}-1)2^A-3,\\
b_N&=V_{M+N+46}.
\end{aligned} \tag{2}
\]
Here \(B\) is the right counter after the long middle-34 SectionResult; \(A\) is the authentic second-q4 width parameter; \(N\) is the exact outer dispatcher index; and \(b_N\) is the exact final right counter. The identities
\[
z=V_{M+43},\quad m=V_{M+44},\quad n=V_{M+45}+1=2^m,\quad
R=V_{M+46}=2^{n-1}-1
\]
give the last line of (2). Moreover \(3\mid N\), since \(L=76\) is even and
\(2^{78}-1\equiv0\pmod3\); put \(k=N/3\).

## Upper tower bound

First, (1) gives \(V_5<T_9\), hence
\[
V_6=2^{V_5}-1\le 2^{T_9-1}-1=T_{10}/2-1.
\]
Since \(V_0,\ldots,V_5<T_9\),
\[
A_0<18+6T_9+T_{10}/2<T_{10}-6,
\]
where the final inequality is immediate for \(T_9\ge16\). Therefore
\[
M<31\,2^{T_{10}-6}=\frac{31}{64}T_{11}<T_{11}/2. \tag{3}
\]
In particular, \(M+49<T_{11}-1\).

Put \(B=V_{M+42}\). By (1),
\[
B<T_{M+46}. \tag{4}
\]
There are exactly \(M+36\) terms in the expression for \(A\) in (2), and each is at most \(B\). Also \(B\ge T_{M+45}+1\), so \(M+36\le B\) and \(2M+59\le2B+59\). Consequently
\[
A\le (M+36)B+2M+59
  \le B^2+2B+59
  <2^{B-1}, \tag{5}
\]
since \(B\) is far above 16. From (4)--(5),
\[
A+78<2^B,\qquad
N<2^{A+78}<2^{2^B}<T_{M+48}. \tag{6}
\]
The last inequality uses \(2^B<2^{T_{M+46}}=T_{M+47}\).

Since \(M+50<T_{M+48}\), (6) implies
\[
M+N+50<T_{M+49}<T_{T_{11}-1}, \tag{7}
\]
where (3) gives \(M+49<T_{11}-1\). Applying (1) once more,
\[
b_N=V_{M+N+46}
 <T_{M+N+50}
 <T_{T_{T_{11}-1}}. \tag{8}
\]
To compare (8) with the next published tower endpoint, put
\[
X=T_{T_{11}-1},\qquad Y=T_X.
\]
Then \(b_N<Y\), while \(T_{T_{11}}=2^X\), and hence
\[
T_{T_{T_{11}}}=T_{2^X}>T_{X+1}=2^{T_X}=2^Y.
\]
As \(Y\) is enormous, \(12Y^2<2^Y\). Therefore
\[
12b_N^2<T_{T_{T_{11}}}. \tag{9}
\]

## From the terminal counter to the complete score

The exact one-dimensional dispatcher formula in
[SectionResultThreeCycle.md](SectionResultThreeCycle.md) gives
\[
D_N\le
6b_N^2+60b_N+(6N^2+57N-66)b_{N-1}
 +48N+90k^2+111k+12(N+1)U+90. \tag{10}
\]
Here \(k=N/3\le N\), \(b_{N-1}<b_N\), \(U\le R\le b_N\), and
\(b_N\ge2^N R\), so \(N\le\log_2 b_N\). For \(b_N\ge2^{64}\), the
nonleading terms in (10) are less than \(b_N^2\): after the substitutions
above they are bounded by
\[
(6N^2+69N+72)b_N+90N^2+159N+90
\le147b_N^{3/2}+339b_N^{1/2}<b_N^2,
\]
where \(N\le\log_2 b_N\le b_N^{1/4}\) for \(b_N\ge2^{64}\).
Thus
\[
D_N<7b_N^2. \tag{11}
\]

The exact score split is
\[
S_{\rm TM1}=C_{\rm root}+D_{\rm root}+D_N(U,R),
\]
where \(D_{\rm root}=\operatorname{drainCost}(R,0)\), and
\(D_N\) includes the complete dispatcher, terminal macro, and the
champion/final-query correction. In particular, those terminal terms are
already included in \(D_N\) and must not be added a second time.

### Explicit root-prefix bound

Put \(B=V_{M+42}\), \(z=2^B-1\), and \(m=2^z-1\).
Unfolding the exact source cost definitions gives
\[
C_{\rm root}=P_{34}+C_M+O+Q,
\]
with
\[
P_{34}\le535\cdot4^B<1000\cdot4^B,\qquad
C_M\le143(B+1)^2,\qquad
O\le86(B+1)^2,
\]
and
\[
Q=D_B+D_z+D_m+1165+12A+27z+15\cdot2^z+3\cdot2^m,
\quad D_t=6\cdot4^t+42\cdot2^t-12t-48.
\]
Here \(D_B=\operatorname{drainCost}(2^B-1,0)\),
\(D_z=\operatorname{drainCost}(2^z-1,0)\), and
\(D_m=\operatorname{drainCost}(2^m-1,0)\). The decomposition is
obtained from the 34-row fixed prefix, the long middle SectionResult,
the outer-LC postlude, and the first-q4/P1 plus q4-tail blocks; see
[Agent44's source-cost expansion](../../communications/agent42/20261120T170825Z_agent44-root-prefix-bound-review.md)
and [the sharpened consolidation](../../communications/agent42/20261120T174518Z_agent44-sharper-tm63-root-bound.md).

For clarity, the fixed prefix itself can be expanded from the source
definitions:
\[
P_{34}=\sum_{\ell=1}^{40}c_\ell+D_{63}+D_{V_7}
       +28424+12A_0+3V_7,
\]
where the \(c_\ell\) are the six pre-middle and 34 middle
proposedIncrementCost terms, \(A_0=\texttt{tm63FirstSection.exponent}\),
and \(V_7=\texttt{tm63FirstSection.right}\). Each row has cost
\[
6\cdot4^b+42\cdot2^b+15+4\mu+12(a+v_2(r))-9b.
\]
For these 40 rows, \(a,b,v_2(r)\le B\) and \(\mu\le2\): the middle-row
valuations satisfy \(v_2(r)\le A_0+4<B\), while the six initial indices
have valuation at most 2. Thus
\[
c_\ell\le6\cdot4^B+42\cdot2^B+23+24B
       \le13\cdot4^B.
\]
This follows from
rootQ4DrainMoves=27959+332+D_{63},
resetCost 3 A_0 V_7=D_{V_7}+133+12A_0+3V_7, and the 34 fixed
middle rows. See
[the q4/drain root](../agent48-counted-inc0/TM63RootQ4Drain.lean),
[the first three counted rows](../agent42-champion-terminal/TM63M0M2RootComposition.lean),
[the fourth row](../agent24-champion-time/TM63M1OddRootComposition.lean),
[the first reset composition](../agent8-rst1prime/TM63M1OddRst1PrimeContinuation.lean),
and [the 34-row continuation](../agent44-tm63-middle/TM63RootMiddle34.lean).
Each \(c_\ell\le13\cdot4^B\), \(D_{63},D_{V_7}\le7\cdot4^B\), and
\(28424+12A_0+3V_7<4^B\) since \(A_0,V_7\le B\) and \(B\ge63\).
Thus \(P_{34}\le(520+14+1)4^B=535\cdot4^B.

Since \(B\le z\le m\), \(m\ge2z\), and
\[
A\le B^2+2B+59\le z^2+2z+59\le m,
\]
we have \(4^B\le2^m\), \((B+1)^2\le2^m\),
\(4^z\le2^m\), and \(2^z=m+1\le2^{m/2}\).
Consequently
\[
P_{34}+C_M+O\le764\cdot2^m,
\]
\[
D_B+D_z\le12\cdot4^z+84\cdot2^z
 \le12\cdot2^m+84\cdot2^{m/2},
\]
\[
D_m\le6\cdot4^m+42\cdot2^m,
\]
and the remaining offsets are at most
\[
1165+39m+15\cdot2^{m/2}+3\cdot2^m.
\]
Adding these inequalities gives
\[
C_{\rm root}
\le6\cdot4^m+821\cdot2^m
 +99\cdot2^{m/2}+39m+1165
 <7\cdot4^m
\tag{11}
\]
For \(m\ge12\), the remainder divided by \(4^m\) is
\[
\frac{821}{2^m}+\frac{99}{2^{3m/2}}+\frac{39m+1165}{4^m}
\le\frac{821}{4096}+\frac{99}{2^{18}}+\frac{1633}{4^{12}}
<\frac13+\frac1{1000}+\frac1{1000}<1;
\]
the three ratios decrease thereafter. This proves the strict bound at
the authentic parameters. Since \(2^m-1\ge m+2\), \(n=2^m\), and \(R=2^{n-1}-1\),
\[
R=2^{2^m-1}-1\ge2^{m+2}-1>3\cdot2^m,
\]
so \(R^2>9\cdot4^m\); also \(b_N\ge R\). Thus
\[
C_{\rm root}<7\cdot4^m<R^2\le b_N^2.
\]

### Remaining score terms

The root drain satisfies
\[
D_{\rm root}\le7\cdot4^{n-1}<14R^2<b_N^2,
\]
because \(n\ge4\) gives \(R=2^{n-1}-1>3\cdot2^{n-3}\), hence
\(R^2>\frac12\,4^{n-1}\), and \(b_N\ge2^N R\) with \(N\ge2\). The dispatcher-plus-terminal
term satisfies \(D_N<7b_N^2\) by (10)--(11); the added fixed
\(+90\) is absorbed by the same \(b_N\ge2^{64}\) remainder
estimate. Therefore the exact score decomposition gives
\[
\boxed{S_{\rm TM1}<9b_N^2<2^Y=T_{X+1}<T_{T_{T_{11}}}.}
\tag{12}
\]
## Lower side and comparison with the published estimate

The exact-V-index lower bound in
[DirectTerminalTetrationBound.md](../agent24-champion-time/DirectTerminalTetrationBound.md)
gives
\[
S_{\rm TM1}\ge
6\bigl(T_{M+N+49}+2\bigr)^2
>T_{M+N+49}. \tag{13}
\]
Here \(M=31\cdot2^{A_0}-36\) and \(N=(2^{78}-1)2^A-3\) are the
authentic middle-dispatcher length and terminal index. The upper-side
estimate gives \(M+N+50<X\), where \(X=T_{T_{11}-1}\), so
\(M+N+49<X+1\) and the lower endpoint is below \(T_{X+1}\. Combining (12)--(13),
\[
\boxed{\quad T_{M+N+49}
 < S_{\rm TM1}
 < T_{X+1}.\quad} \tag{14}
\]
This lower endpoint strictly improves the published left endpoint
\(T_{T_{T_{10}}}\), because \(M+N+49>T_{M+46}>T_{T_{10}}\).
For comparison, the published mxdys interval is
\[
2\uparrow\uparrow2\uparrow\uparrow2\uparrow\uparrow10
 < \text{time/score} <
2\uparrow\uparrow2\uparrow\uparrow2\uparrow\uparrow11.
\]
See the
[BB(6) champion analysis](https://wiki.bbchallenge.org/wiki/1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE)
for the published estimate and the four-machine family comparison.

## Scope

This is a mathematical bound on the **one TM1 champion trajectory**, conditional
on the exact source-root and dispatcher compositions. It is not a BB(6)
upper bound: all other six-state machines remain to be decided. The source
composition and its transitive axiom profile still require the prescribed
local Lean preflight; this paper derivation must remain in im-results until
that succeeds.
