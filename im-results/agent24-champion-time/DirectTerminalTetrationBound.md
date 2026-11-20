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


## Exact V-index refinement of the terminal lower bound

The coarse \(H=T_{10}\) estimate above can be sharpened without replacing the
source-defined sequence by tetration notation. Define
\[
V_0=63,\qquad V_{j+1}=2^{V_j}-1.
\]
The first SectionResult is \(\operatorname{sectionResult}(7,2,6,63)\).
Its marker sequence is \(2,1,0,2,1,0,2\), so the seven additive marker
offsets sum to \(12\). Consequently its exponent and final right counter
are exactly
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
The subsequent marker-1 dispatcher has exactly
\[
M=16\cdot\texttt{tm63RootResidueSixK}-20
=31\cdot2^{A_0}-36
\]
updates: the root index is \(K=31\cdot2^{A_0-3}-1\), is odd, and
\(\texttt{tm63RootResidueSixK}=K/2=31\cdot2^{A_0-4}-1\).
Starting at right \(V_{42}\), those \(M\) updates end at \(V_{M+42}\).

The marker-1 S0 reset width is
\[
A=\texttt{middle34Result.exponent}
  +\texttt{middle34Result.right}+2.
\]
Every SectionResult exponent update adds the current right counter plus
either \(1\) or \(2\). Dropping only these positive offsets, the 34 middle
updates contribute at least \(\sum_{j=8}^{41}V_j\), the \(M\) dispatcher
updates contribute at least \(\sum_{j=42}^{M+41}V_j\), and the final reset
adds \(V_{M+42}+2\). Therefore
\[
\boxed{
A\ge A_{\min}:=
V_7+\sum_{j=8}^{M+42}V_j+2.
}
\]
The earlier first-section exponent \(A_0\) does not appear as an additive
term in \(A_{\min}\): the authentic reset explicitly replaces the next
SectionResult exponent by the preceding right counter \(V_7\). It enters
the bound through the exact dispatcher length \(M\).

For the authentic \(L=76\) q4Tail route, the terminal index is
\[
N=2^A(2^{78}-1)-3
\]
and hence
\[
N\ge N_0:=(2^{78}-1)2^{A_{\min}}-3.
\]
The terminal right counter starts at \(R\ge2\) and makes \(N\) updates
\(b_{j+1}=2^{b_j}-1\). Thus \(b_N\ge T_N+1\ge T_{N_0}+1\).
The final dispatcher increment alone contributes
\(6\cdot4^{b_{N-1}}=6(b_N+1)^2\), giving the sharper conditional bound
\[
\boxed{
S\ge6\left(T_{N_0}+2\right)^2,\quad
N_0=(2^{78}-1)2^{\,V_7+\sum_{j=8}^{M+42}V_j+2}-3,\quad
M=31\cdot2^{A_0}-36,\quad
A_0=18+\sum_{j=0}^{6}V_j.
}
\]
This exact V-index expression is stronger than the \(H=T_{10}\) corollary.
Its source dependencies are the seven-step first-section recurrence,
the 34 middle-row composition, the exact \(M\)-step SectionResult
dispatcher, and the marker-1 reset identity. It remains conditional on
the uncompiled authentic-root/source-composition closure.

## Consequence for the arbitrary-A terminal dispatcher

For the authentic length \(L=76\), the direct q4Tail terminal route has
\[
N=2^A(2^{78}-1)-3.
\]
Since \(2^{78}-1\ge3\), \(N>2^A\). Since \(A> T_H\),
\[
N>2^{T_H}=T_{H+1}.
\]
Hence \(N\ge T_{H+1}+1\).

The q4Tail inner parameter satisfies \(z=\texttt{rootMarker1Z}\ge3\), so
\[
n=2^{2^z-1}\ge2^7=128,\qquad
R=2^{n-1}-1\ge2.
\]
The terminal SectionResult starts with right counter \(R\) and performs \(N\)
updates \(b_{j+1}=2^{b_j}-1\). Therefore
\[
b_N\ge T_N+1
\ge T_{\,T_{H+1}+1}+1.
\]

The exact dispatcher-cost expression in
[SectionResultThreeCycle.md](../agent42-q4-s0-drain/SectionResultThreeCycle.md)
contains the final increment contribution
\[
6\cdot4^{b_{N-1}}
=6(2^{b_{N-1}})^2
=6(b_N+1)^2,
\]
and all other terms in the displayed summed cost are nonnegative. The root prefix,
counted drain, terminal macro, and champion-attainability correction are also
nonnegative. Consequently, **conditional on the authentic-root and complete
dispatcher source composition being valid**, the attained TM1 champion score
satisfies the stronger bound
\[
\boxed{
S\ge6\left(T_{\,T_{\,H+1}+1}+2\right)^2,
\qquad H=T_{10}.
}
\]
Because \(H=T_{10}>T_4=65536\), this is strictly stronger than the coarse
\(2\uparrow\uparrow\uparrow5\) comparison. It uses the full seven-step first
SectionResult, rather than only its first exponent update.

## What this does and does not establish

This is an exact paper derivation from the current source-level recurrences and
root index identities. It sharpens the conditional tower-height estimate, but
it does **not** prove the root/dispatcher source closure, establish an exact
primitive-step numeral, or provide a universal six-state upper bound. The
authentic-root, q4Tail/S0, 24-class dispatcher, counted-drain, and terminal
dependency closure remains uncompiled as a whole. Keep this derivation in
**im-results/** until the exact local preflight and transitive axiom audit pass.
