# Conditional tetration-scale lower bound for the direct TM63 terminal route

**Status:** paper-level derivation conditional on the source composition in [TM63GeneralQ4TerminalComposition.lean](../agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean). It is not a compiled theorem, a new published lower bound, or a BB(6) solution. Its purpose is to show that the arbitrary-A route reaches at least the known (2\uparrow\uparrow\uparrow5) scale; it does not rely on expanding any astronomical numeral.

## Tetration comparison

Define
[
T_1=2,\qquad T_{j+1}=2^{T_j}.
]
Thus (T_j=2\uparrow\uparrow j), (2\uparrow\uparrow\uparrow4=T_{65536}), and
[
2\uparrow\uparrow\uparrow5=T_{T_{65536}}.
]

For the right-counter recurrence
[
x_0\ge2,\qquad x_{j+1}=2^{x_j}-1,
]
we have
[
x_j\ge T_j+1\qquad(j\ge1).
]
Indeed, the base case is (x_1\ge3=T_1+1). If (x_j\ge T_j+1), then
[
x_{j+1}\ge2^{T_j+1}-1
=2T_{j+1}-1\ge T_{j+1}+1,
]
since (T_{j+1}\ge2).

## The first authentic SectionResult stage already supplies more than 65,536 decrements

Let
[
A_0=\texttt{tm63FirstSection.exponent},\qquad
\texttt{tm63FirstSection}=\operatorname{sectionResult}(7,2,6,63).
]
The first SectionResult increment starts at marker (2), so its exponent update is (6+63+2=71). Every later exponent update adds a nonnegative right counter and either one or two. Hence (A_0\ge71).

The root countdown arithmetic defines
[
K=31\cdot2^{A_0-3}-1,\qquad
r=\lfloor K/2\rfloor
=31\cdot2^{A_0-4}-1.
]
Therefore
[
r\ge31\cdot2^{67}-1,
\qquad M=16r-20\ge65536.
]
The authentic middle-34 endpoint has initial right counter (B_0=\texttt{tm63MiddleAfter34B}\ge2), as stated by the source-draft lemma `tm63MiddleAfter34B_ge_two` in [TM63RootMarker1Endpoint.lean](../agent44-tm63-middle/TM63RootMarker1Endpoint.lean). The complete middle-34 SectionResult dispatcher performs exactly (M) right-counter updates (x\mapsto2^x-1). Its final right counter (B_1) consequently satisfies
[
B_1\ge T_M+1\ge T_{65536}+1.
]

The canonical marker-1 reset parameter is
[
A=\texttt{rootMarker1A}
=\texttt{middle34Result.exponent}
 +\texttt{middle34Result.right}+2
\ge B_1+2>T_{65536}.
]

## The arbitrary-A terminal dispatcher exceeds the published scale

For the authentic length (L=76), the direct q4Tail terminal route has
[
N=2^A(2^{78}-1)-3.
]
Since (A\ge2), (2^{78}-1\ge3), and hence (N\ge2^A). From (A>T_{65536}),
[
N>2^{T_{65536}}=T_{65537},
\qquad N-1\ge T_{65536}.
]

The q4Tail inner parameter satisfies (z=\texttt{rootMarker1Z}\ge3), so
[
n=2^{2^z-1}\ge2^7=128,
\qquad R=2^{n-1}-1\ge2.
]
The terminal SectionResult starts with right counter (R) and performs (N) updates (b_{j+1}=2^{b_j}-1). Applying the recurrence bound above to its first (N-1) updates gives
[
b_{N-1}\ge T_{N-1}+1
\ge T_{T_{65536}}+1
=2\uparrow\uparrow\uparrow5+1.
]

The terminal exponent is
[
E=U+\sum_{j=0}^{N-1}(b_j+\epsilon_j),
\qquad \epsilon_j\in\{1,2\},
]
so (E\ge b_{N-1}>2\uparrow\uparrow\uparrow5). The terminal macro uses
[
\operatorname{terminalMoves}(W,E)=59+12(W+E)>E.
]
All root-prefix, counted-drain and dispatcher costs are nonnegative. Thus, **conditional on the source-level root and dispatcher composition being valid**, the attained score satisfies
[
S>2\uparrow\uparrow\uparrow5.
]

## What this does and does not establish

This comparison uses only the exact SectionResult right-counter recurrence, the root index formula, the root lower bound (B_0\ge2), and the arbitrary-A terminal index. It shows that the direct route is not a weaker terminal branch: if its complete Lean source closure is accepted, it reproduces at least the published (2\uparrow\uparrow\uparrow5) lower-bound scale without evaluating the enormous score.

It does **not** prove the source closure, establish the exact primitive-step numeral, improve the published asymptotic lower bound, or provide a universal upper bound for six-state machines. The relevant source modules remain uncompiled as a complete dependency closure. Keep this derivation in `im-results/` until the exact local preflight and transitive axiom audit pass.
