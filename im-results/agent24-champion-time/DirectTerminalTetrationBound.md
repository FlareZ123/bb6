# Conditional tower-height lower bound for the direct TM63 terminal route

**Status:** paper-level derivation conditional on the source composition in [TM63GeneralQ4TerminalComposition.lean](../agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean). The normalized tm2 run is transported to the actual TM1 champion by [ChampionRootBridge.lean](../agent48-champion-root/ChampionRootBridge.lean); the Attainable adapter's \(+7\) is the six-transition root offset plus the final undefined-query step. This is not a compiled theorem, a new accepted BB(6) lower bound, or a BB(6) solution. The purpose is to sharpen the conditional size estimate without expanding astronomical numerals.

## Tetration comparison

Define
\[
T_1=2,\qquad T_{j+1}=2^{T_j}.
\]
Thus \(T_j=2\uparrow\uparrow j\), \(T_4=65536\), and
\[
2\uparrow\uparrow\uparrow4=T_{65536},\qquad
2\uparrow\uparrow\uparrow5=T_{T_{65536}}.
\]

For the right-counter recurrence
\[
x_0\ge2,\qquad x_{j+1}=2^{x_j}-1,
\]
we have
\[
x_j\ge T_j+1\qquad(j\ge1).
\]
The base case is \(x_1\ge3=T_1+1\). If \(x_j\ge T_j+1\), then
\[
x_{j+1}\ge2^{T_j+1}-1
=2T_{j+1}-1\ge T_{j+1}+1,
\]
since \(T_{j+1}\ge2\).

## Stronger authentic-root estimate from all seven first-section updates

Let
\[
A_0=\texttt{tm63FirstSection.exponent},\qquad
\texttt{tm63FirstSection}=\operatorname{sectionResult}(7,2,6,63).
\]
Write \((a_i,b_i)\) for the exponent and right-counter fields after \(i\) updates in this seven-step section. Then
\[
b_0=63,\qquad b_{i+1}=2^{b_i}-1,\qquad
a_{i+1}=a_i+b_i+\epsilon_i,\quad \epsilon_i\in\{1,2\}.
\]
Since \(T_3=16\), \(b_0=63\ge T_3+1\). The same induction as above, with the index shifted by three, gives
\[
b_i\ge T_{i+3}+1\qquad(0\le i\le6).
\]
The seventh exponent update consumes \(b_6\), so
\[
A_0=a_7\ge b_6\ge T_9+1.
\]

The root countdown arithmetic defines
\[
K=31\cdot2^{A_0-3}-1,\qquad
r=\lfloor K/2\rfloor=31\cdot2^{A_0-4}-1.
\]
Here \(K\) is odd by the existing root arithmetic, and \(A_0\ge5\). The middle-34 dispatcher length is therefore exactly
\[
M=16r-20=31\cdot2^{A_0}-36.
\]
Put \(H=T_{10}=2^{T_9}\). From \(A_0\ge T_9+1\),
\[
M\ge31\cdot2^{T_9+1}-36=62H-36>H.
\]

The authentic middle-34 endpoint has initial right counter
\(B_0=\texttt{tm63MiddleAfter34B}\ge2\), as stated by the source-draft lemma
**tm63MiddleAfter34B\_ge\_two** in
[TM63RootMarker1Endpoint.lean](../agent44-tm63-middle/TM63RootMarker1Endpoint.lean).
Its SectionResult dispatcher performs exactly \(M\) updates
\(x\mapsto2^x-1\). Thus its final right counter \(B_1\) satisfies
\[
B_1\ge T_M+1>T_H+1.
\]
The canonical marker-1 reset width is
\[
A=\texttt{rootMarker1A}
=\texttt{middle34Result.exponent}
+\texttt{middle34Result.right}+2
\ge B_1+2>T_H.
\]


## Exact V-index formula for the authentic terminal width

Define
\[
V_0=63,\qquad V_{j+1}=2^{V_j}-1.
\]
All \(V_j\) are odd. The first SectionResult is
\(\operatorname{sectionResult}(7,2,6,63)\), with marker sequence
\(2,1,0,2,1,0,2\). Its seven exponent offsets sum to
\(2+2+1+2+2+1+2=12\), so its exponent and final right counter are exactly
\[
A_0=18+\sum_{j=0}^{6}V_j,\qquad B_{\rm first}=V_7.
\]

The authentic middle-section reset explicitly starts the next SectionResult
at exponent \(V_7\) and right counter \(V_8\):
\[
\texttt{tm63MiddleSection}
=\operatorname{sectionResult}(\texttt{tm63Index1},2,V_7,V_8).
\]
The 34 source-connected middle increments consume right counters
\(V_8,\ldots,V_{41}\), leaving
\[
\texttt{tm63MiddleAfter34B}=V_{42}.
\]
Their marker sequence is \(2,1,0\) repeated 11 times, followed by one
additional marker 2. Their exponent offsets therefore sum exactly to
\(11(2+2+1)+2=57\).

The subsequent marker-1 dispatcher has exactly
\[
M=16\cdot\texttt{tm63RootResidueSixK}-20
=31\cdot2^{A_0}-36
\]
updates: the root index is \(K=31\cdot2^{A_0-3}-1\), is odd, and
\(\texttt{tm63RootResidueSixK}=K/2=31\cdot2^{A_0-4}-1\).
Since \(A_0\) is odd, \(2^{A_0}\equiv2\pmod3\), hence \(M\equiv2\pmod3\).
Starting at right \(V_{42}\), the \(M\) updates end at \(V_{M+42}\).
Their marker sequence starts \(1,0,2\), with exponent offsets \(2,1,2\).
Writing \(M=3q+2\), the exact offset sum is
\[
5q+3=\frac{5M-1}{3}.
\]

The marker-1 S0 reset width is exactly
\[
A=\texttt{middle34Result.exponent}
  +\texttt{middle34Result.right}+2.
\]
The initial exponent is \(V_7\); the 34 middle increments contribute
\(\sum_{j=8}^{41}V_j+57\); the \(M\)-step dispatcher contributes
\(\sum_{j=42}^{M+41}V_j+(5M-1)/3\); and the reset adds
\(V_{M+42}+2\). Therefore the full width is not merely bounded below:
\[
\boxed{
A=V_7+\sum_{j=8}^{M+42}V_j+\frac{5M+176}{3}
=V_7+\sum_{j=8}^{M+42}V_j+\frac{155\cdot2^{A_0}-4}{3}.
}
\]
In particular, \(A_0\) enters the reset width through the exact dispatcher
length \(M\); it is not carried additively across the authentic reset.

For the authentic \(L=76\) q4Tail route, the terminal index is exactly
\[
N=(2^{78}-1)2^A-3.
\]
The q4Tail S1 encoding is exactly four more applications of the same
right-counter map \(f(x)=2^x-1\). With \(B=V_{M+42}\), its definitions give
\[
z=2^B-1=V_{M+43},\qquad
I=\texttt{q4TerminalInnerCount}(z)=2^{2^z-1}.
\]
But \(2^z-1=V_{M+44}\), so
\[
I=2^{V_{M+44}}=V_{M+45}+1,\qquad
R=\texttt{q4TerminalRight}(z)=2^{I-1}-1=V_{M+46}.
\]
Thus the terminal dispatcher does not merely start above a tower lower
bound: its initial right counter is exactly the next V-sequence term
\(V_{M+46}\). Since its N updates also use \(f(x)=2^x-1\), the final
right counter is exactly
\[
b_N=V_{M+N+46}.
\]
In the exact one-dimensional dispatcher cost formula, the final summand
\(j=N-1\) has coefficient \(12(N-j)-9=3\). Since
\(b_N=V_{M+N+46}\) and \(b_{N-1}=V_{M+N+45}\), that entire summand is
\[
6\cdot4^{b_{N-1}}+42\cdot2^{b_{N-1}}+3b_{N-1}
=
6(V_{M+N+46}+1)^2
+42(V_{M+N+46}+1)
+3V_{M+N+45}.
\]
The coefficient (3) is for the **combined dispatcher-plus-terminal score**,
not the isolated last increment: the last increment contributes
(-9b_{N-1}), while the terminal macro
\(\texttt{terminalMoves}=59+12(L+E)\), with
\(E=U+\sum_{j=0}^{N-1}b_j+5k\), contributes
\(+12b_{N-1}\). Their sum is (+3b_{N-1}).

All other dispatcher summands and the root/drain prefix costs are
nonnegative. Therefore the stronger conditional score bound is
\[
\boxed{
S\ge
6(V_{M+N+46}+1)^2
+42(V_{M+N+46}+1)
+3V_{M+N+45}.
}
\]
In particular, the quadratic term alone gives the simpler bound
\(S\ge6(V_{M+N+46}+1)^2\).

This exact V-index expression sharpens the earlier \(A_{\min}\) bound by
retaining every marker offset. It is still conditional on the uncompiled
authentic-root/source-composition closure; it is not an accepted BB(6)
lower-bound theorem.
## Stronger consequence from retaining the exact V-index

The recurrence estimate can be started at the actual \(V_0=63\), rather
than at an arbitrary \(x_0\ge2\). Since \(63\ge T_3+1\), induction gives
\[
V_j\ge T_{j+3}+1\qquad(j\ge0).
\]
The exact width formula above contains its final summand
\(B=V_{M+42}\), so
\[
A\ge B\ge T_{M+45}+1.
\]
For the authentic terminal index
\[
N=(2^{78}-1)2^A-3,
\]
the coefficient \(2^{78}-1\ge3\) gives \(N>2^A\). Hence
\[
N>2^{T_{M+45}}=T_{M+46},
\qquad
N\ge T_{M+46}+1.
\]

Retain the exact final right-counter identity
\(b_N=V_{M+N+46}\). Applying the same recurrence estimate directly,
\[
b_N\ge T_{M+N+49}+1.
\]
The exact dispatcher-plus-terminal cost contains the final-increment
contribution \(6(b_N+1)^2\), and every other term in the score is
nonnegative. Therefore
\[
\boxed{
S\ge6\bigl(T_{M+N+49}+2\bigr)^2
  >T_{M+N+49}.
}
\]
This is stronger than the intermediate endpoint \(T_{T_{M+46}}\):
indeed \(N\ge T_{M+46}+1\), so \(M+N+49>T_{M+46}\).

The sharper upper-side estimate in
[TM63PublishedTowerSandwich.md](../agent42-q4-s0-drain/TM63PublishedTowerSandwich.md)
gives \(M+N+50<T_J\), where
\[
J=2^{\frac12\sqrt{T_{10}}+\frac12T_9+T_8+T_7+T_6+T_5+80}.
\]
Hence
\[
T_{M+N+49}<T_{T_J},
\]
which is the current conditional upper endpoint.
It also strictly exceeds the published left endpoint
\(T_{T_{T_{10}}}\), since \(M+N+49>T_{M+46}>T_{T_{10}}\).

## What this does and does not establish

This is an exact paper derivation from the current source-level recurrences and
root index identities. It sharpens the conditional tower-height estimate, but
it does **not** prove the root/dispatcher source closure, establish an exact
primitive-step numeral, or provide a universal six-state upper bound. The
authentic-root, q4Tail/S0, 24-class dispatcher, counted-drain, and terminal
dependency closure remains uncompiled as a whole. Keep this derivation in
**im-results/** until the exact local preflight and transitive axiom audit pass.
