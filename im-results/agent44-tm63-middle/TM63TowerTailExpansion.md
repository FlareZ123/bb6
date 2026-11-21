# Tower-tail domination and a four-scale TM63 score expansion

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
Then \(D_N=10N^2+37N+90+12(N+1)U+\sum_{j=0}^{N-1}T_j\).

## General tail-domination lemma

For any integer \(r\) with
\[
2\le r\le N,\qquad N\le b_{r-1},
\]
separate the high-index summands \(T_{r-1},\ldots,T_{N-1}\) and put
\[
E_r=C_{\rm root}+D_{\rm root}
 +10N^2+37N+90+12(N+1)U
 +\sum_{j=0}^{r-2}T_j.
\]
Then
\[
\boxed{0\le E_r<\frac{b_r^2}{100}.}
\]

**Proof.** Put \(x=b_{r-1}\). For \(j\le r-2\), monotonicity gives \(b_{j+1},b_j\le x\), and \(r-1\le N\le x\). The exponential part of each omitted summand satisfies
\[
6\cdot4^{b_j}+42\cdot2^{b_j}
=6(b_{j+1}+1)^2+42(b_{j+1}+1)
\le48(x+1)^2\le192x^2.
\]
There are at most \(x\) such summands, so their exponential parts total at most \(192x^3\). The sum of their positive linear coefficients is less than \(6N^2\); since \(b_j\le x\), their linear parts total less than \(6x^3\).

For \(N\ge256\),
\[
10N^2+37N+90<11N^2\le11x^2.
\]
Also \(U\le R\le x\), so \(12(N+1)U\le12(x+1)x\le24x^2\), and the root contribution is less than \(15R^2\le15x^2\). Hence
\[
0\le E_r<198x^3+50x^2<248x^3.
\]
Since \(x\ge R\ge63\), \(b_r=2^x-1\ge2^{x-1}\), and
\[
248x^3<\frac{4^{x-1}}{100}
\le\frac{b_r^2}{100}.
\]
The first inequality holds for \(x\ge63\) (indeed from \(x=16\) onward, because \(4^{x-1}/x^3\) is increasing there). This proves the claim. \(\square\)

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
where
\[
\boxed{0\le E_4<\frac{b_{N-3}^2}{100}.}
\]
Equivalently, with \(u=b_{N-3}\), the entire root cost, polynomial correction, and all dispatcher summands below the four displayed summands contribute less than one percent of \(u^2\).

For comparison, applying the same lemma with \(r=N-2\) gives the earlier three-scale corollary with remainder below \(b_{N-2}^2/100\). The four-scale statement is strictly sharper. Since \(t=2^u-1\), \(u=2^v-1\), and \(\ell=2^t-1\), the expansion exposes successive levels of the tower rather than absorbing them into the previous coarse \(O((\log\ell)\ell^2)\) bound.

## Evidence boundary

This is a mathematical derivation from the already-recorded exact symbolic cost identity and root-prefix estimate. It introduces no new simulation claim and no Lean theorem. The root-to-q4Tail/dispatcher source chain and transitive axiom audit remain unaccepted; this is not yet an unconditional champion score. Keep it in im-results/. It does not decide any other six-state machine and does not prove the universal upper bound.
