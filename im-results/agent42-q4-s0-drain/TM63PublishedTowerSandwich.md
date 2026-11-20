# TM63 exact recurrence: a source-conditional published tower sandwich

**Status:** intermediate mathematical derivation. Every statement about the actual TM1 run is conditional on the authentic blank-root/source-composition chain in `TM63GeneralQ4TerminalComposition.lean`. This note does not certify that uncompiled Lean composition and does not give a universal BB(6) upper bound.

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
Here (B) is the right counter after the long middle-34 SectionResult; (A) is the authentic second-q4 width parameter; (N) is the exact outer dispatcher index; and (b_N) is the exact final right counter. The identities (z=V_{M+43}), (m=V_{M+44}), (n=V_{M+45}+1), and (R=V_{M+46}) give the last line of (2).

## Upper tower bound

First, (1) gives (V_5<T_9), hence
\[
V_6=2^{V_5}-1\le 2^{T_9-1}-1=T_{10}/2-1.
\]
Since (V_0,\ldots,V_5<T_9),
\[
A_0<18+6T_9+T_{10}/2<T_{10}-6,
\]
where the final inequality is immediate for (T_9\ge 16). Therefore
\[
M<31\,2^{T_{10}-6}=\frac{31}{64}T_{11}<T_{11}/2. \tag{3}
\]
In particular, (M+49<T_{11}-1).

Put (B=V_{M+42}). By (1),
\[
B<T_{M+46}. \tag{4}
\]
There are exactly (M+36) terms in the expression for (A) in (2), and each is at most (B). Also (B\ge T_{M+45}+1), so (M+36\le B) and (2M+59\le2B+59). Consequently
\[
A\le (M+36)B+2M+59
  \le B^2+2B+59
  <2^{B-1}, \tag{5}
\]
since (B\) is far above 16. From (4)--(5),
\[
A+78<2^B,\qquad
N<2^{A+78}<2^{2^B}<T_{M+48}. \tag{6}
\]
The last inequality uses (2^B<2^{T_{M+46}}=T_{M+47}).

Since (M+50<T_{M+48}), (6) implies
\[
M+N+50<T_{M+49}<T_{T_{11}-1}, \tag{7}
\]
where (3) gives (M+49<T_{11}-1). Applying (1) once more,
\[
b_N=V_{M+N+46}
 <T_{M+N+50}
 <T_{T_{T_{11}-1}}. \tag{8}
\]
Thus
\[
10b_N^2<T_{T_{T_{11}}}. \tag{9}
\]
Indeed, with (x=T_{T_{T_{11}-1}}), (8) gives (b_N<x), while
(10x^2<2^x=T_{T_{T_{11}}}) for this enormous (x).

## From the terminal counter to the complete score

The exact one-dimensional dispatcher formula in
[SectionResultThreeCycle.md](SectionResultThreeCycle.md) gives
\[
D_N\le
6b_N^2+60b_N+(6N^2+57N-66)b_{N-1}
 +48N+90k^2+111k+12(N+1)U. \tag{10}
\]
Here (k\le2N), (b_{N-1}<b_N), (U\le R\le b_N), and
(b_N\ge2^N R), so (N\le\log_2 b_N). The nonleading terms in (10)
are therefore (O(b_N\log^2 b_N)), and the exact parameters are far
beyond the fixed threshold at which
\[
D_N<7b_N^2. \tag{11}
\]

The remaining costs are smaller than (b_N^2):

- the root-to-q4 prefix is (O(4^m)), while
  (R=2^{2^m-1}-1) and (b_N\ge R), so (O(4^m)<R^2\le b_N^2);
- the counted root drain is (O(R^2)), and (b_N\ge2^N R) with
  (N\ge2);
- the terminal macro is (59+12(L+E)), with
  (E=U+\sum_{j<N}b_j+5k\le U+Nb_N+10N), hence it is
  (O(Nb_N)=o(b_N^2));
- the champion-root and final-query correction is (+7).

The constants in the root-prefix (O(4^m)) bound come from the finite
source macros displayed in the root-cost definitions; the separation
(R^2/4^m\to\infty) is already overwhelming at the authentic parameters.
Combining these bounds with (11), the complete conditional champion score
satisfies
\[
S_{\rm TM1}<10b_N^2<T_{T_{T_{11}}}. \tag{12}
\]

## Lower side and comparison with the published estimate

The stronger lower bound in
[DirectTerminalTetrationBound.md](../agent24-champion-time/DirectTerminalTetrationBound.md)
gives, with (H=T_{10}),
\[
S_{\rm TM1}\ge
6\bigl(T_{T_{H+1}+1}+2\bigr)^2
>T_{T_{T_{10}}}. \tag{13}
\]
Combining (12)--(13),
\[
\boxed{\quad T_{T_{T_{10}}}
 < S_{\rm TM1}
 < T_{T_{T_{11}}}.\quad} \tag{14}
\]
This is the exact (T)-notation form of the published mxdys interval
\(2\,\!\uparrow\!\uparrow\,2\,\!\uparrow\!\uparrow\,2\,\!\uparrow\!\uparrow\,10
 < \text{time/score} <
2\,\!\uparrow\!\uparrow\,2\,\!\uparrow\!\uparrow\,2\,\!\uparrow\!\uparrow\,11\).
The source-recurrence lower side (13) is stronger than the left endpoint
of that coarse published interval. See the
[BB(6) champion analysis](https://wiki.bbchallenge.org/wiki/1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE)
for the published estimate and the four-machine family comparison.

## Scope

This is a mathematical bound on the **one TM1 champion trajectory**, conditional
on the exact source-root and dispatcher compositions. It is not a BB(6)
upper bound: all other six-state machines remain to be decided. The source
composition and its transitive axiom profile still require the prescribed
local Lean preflight; this paper derivation must remain in `im-results/`
until that succeeds.
