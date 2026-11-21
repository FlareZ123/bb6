# Quadratic tower-tail bound and four-scale TM63 score expansion

**Status:** paper-level algebraic consequence of the existing exact, source-conditional score decomposition. It does not compile the authentic TM63 itinerary, certify an unconditional Lean Attainable witness, or establish a BB(6) upper bound.

## Exact score identity being refined

Let
\[
b_0=R,\qquad b_{j+1}=2^{b_j}-1,
\]
where \(N\ge256\), \(3\mid N\), \(R\ge63\), and \(0\le U\le R\). The existing conditional score decomposition is
\[
S=C_{\rm root}+D_{\rm root}+D_N,
\]
with
\[
D_N=10N^2+37N+90+12(N+1)U
+\sum_{j=0}^{N-1}
\left(6\cdot4^{b_j}+42\cdot2^{b_j}
 +(12(N-j)-9)b_j\right),
\]
and the root estimates give
\[
0\le C_{\rm root}+D_{\rm root}<\frac{133}{9}R^2<15R^2.
\]
These hypotheses and the source boundary are recorded in [TM63ScoreAsymptotic.md](../agent42-q4-s0-drain/TM63ScoreAsymptotic.md) and [TM63PublishedTowerSandwich.md](../agent42-q4-s0-drain/TM63PublishedTowerSandwich.md).

The recurrence gives the exact identity
\[
6\cdot4^{b_j}+42\cdot2^{b_j}
=6b_{j+1}^2+54b_{j+1}+48.
\]
Define
\[
T_j=6b_{j+1}^2+54b_{j+1}+48
 +(12(N-j)-9)b_j.
\]
Then
\[
D_N=10N^2+37N+90+12(N+1)U+\sum_{j=0}^{N-1}T_j.
\]

## General quadratic tail-domination lemma

For any integer \(r\) with
\[
2\le r\le N,\qquad N\le b_{r-1},
\]
retain the high-index summands \(T_{r-1},\ldots,T_{N-1}\), and put
\[
E_r=C_{\rm root}+D_{\rm root}
 +10N^2+37N+90+12(N+1)U
 +\sum_{j=0}^{r-2}T_j.
\]
Then the stronger bound is
\[
\boxed{0\le E_r<45b_{r-1}^2.}
\]

**Proof.** Put \(x=b_{r-1}\). Since \(b_0=R\ge63\) and \(b_{j+1}=2^{b_j}-1\ge2b_j\), the sequence at least doubles at each step. Thus
\[
\sum_{j=0}^{r-2}b_{j+1}\le2x,\qquad
\sum_{j=0}^{r-2}b_{j+1}^2\le\frac43x^2,\qquad
\sum_{j=0}^{r-2}b_j\le x,\qquad R\le\frac{x}{2}.
\]
There are \(r-1\le N\le x\) omitted summands.

Using
\[
6\cdot4^{b_j}+42\cdot2^{b_j}
=6b_{j+1}^2+54b_{j+1}+48,
\]
their exponential parts total at most
\[
6\cdot\frac43x^2+54\cdot2x+48x
=8x^2+156x<11x^2
\]
because \(x\ge63\).

Each positive linear coefficient \(12(N-j)-9\) is less than \(12N\le12x\). Hence all omitted linear parts total less than
\[
12x\sum_{j=0}^{r-2}b_j\le12x^2.
\]
The remaining terms satisfy
\[
10N^2+37N+90<11x^2,
\]
\[
12(N+1)U\le12(x+1)\frac{x}{2}\le7x^2,
\]
and
\[
C_{\rm root}+D_{\rm root}<15R^2
\le\frac{15}{4}x^2<4x^2.
\]
Adding the five bounds gives
\[
0\le E_r<(11+12+11+7+4)x^2=45x^2.
\]
This proves the lemma. \(\square\)

The earlier cubic comparison \(E_r< b_r^2/100\) follows immediately but is substantially weaker: the residual is quadratic in the largest omitted tower variable \(b_{r-1}\), not merely small relative to the next tower \(b_r\).

## Four-scale expansion at the authentic index

The elementary growth bound \(b_j\ge2^jR\) implies
\[
b_{N-4}\ge2^{N-4}R\ge N
\]
for \(N\ge256\), so the tail lemma applies with \(r=N-3\).

Write
\[
b=b_N,\qquad \ell=b_{N-1},\qquad
t=b_{N-2},\qquad u=b_{N-3},\qquad v=b_{N-4}.
\]
The last four summands are exactly
\[
\begin{aligned}
T_{N-1}&=6b^2+54b+48+3\ell,\\
T_{N-2}&=6\ell^2+54\ell+48+15t,\\
T_{N-3}&=6t^2+54t+48+27u,\\
T_{N-4}&=6u^2+54u+48+39v.
\end{aligned}
\]
Consequently,
\[
\boxed{
\begin{aligned}
S={}&6b_N^2+54b_N
 +6b_{N-1}^2+57b_{N-1}\\
 &+6b_{N-2}^2+69b_{N-2}
 +6b_{N-3}^2+81b_{N-3}\\
 &+39b_{N-4}+192+E_4,
\end{aligned}}
\]
with the sharpened remainder
\[
\boxed{0\le E_4<45b_{N-4}^2.}
\]
The former \(E_4<b_{N-3}^2/100\) estimate is an immediate, much weaker corollary because \(b_{N-3}=2^{b_{N-4}}-1\).

More generally, the same lemma permits any cutoff \(r\) satisfying \(N\le b_{r-1}\): retain every summand from \(T_{r-1}\) through \(T_{N-1}\), and the complete remaining root/polynomial/low-index tail is less than \(45b_{r-1}^2\). This gives a tunable tower expansion rather than a single fixed truncation.

## Evidence boundary

This is a mathematical derivation from the already-recorded exact symbolic cost identity and root-prefix estimate. It introduces no new simulation claim and no Lean theorem. The root-to-q4Tail/dispatcher source chain and transitive axiom audit remain unaccepted; this is not yet an unconditional champion score. Keep it in im-results/. It does not decide any other six-state machine and does not prove the universal upper bound.
