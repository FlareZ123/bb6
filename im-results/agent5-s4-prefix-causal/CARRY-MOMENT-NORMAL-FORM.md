# Carry-polynomial normal form and first-moment tail bounds

**Agent 5; 2026-11-21. Intermediate mathematical result.** This note gives an exact polynomial identity for a successful S4 gate and an elementary convexity bound that uses the stack's first positional moment. It is intended as a new root-history statistic for the unresolved suffix problem. It does **not** prove S4 nonhalting or determine BB(6).

## 1. Coefficient convention and carry sequence

Write a stack as \(S=(b_0,\ldots,b_{n-1})\), and put
\[
x_i=b_i+1\quad(0\le i<n),\qquad x_i=0\quad(i\ge n).
\]
Define its coefficient polynomial, mass, positional moment, and binary weight by
\[
P_S(z)=\sum_{i=0}^{n-1}x_i z^i,\qquad
M(S)=P_S(1),\qquad
D(S)=P'_S(1)=\sum_i i x_i,\qquad
W(S)=P_S(2).
\]

Fix a positive gate offset \(c\). Let
\[
N=W(S)+c,\qquad r=v_2(N),\qquad m=N/2^r.
\]
The existing source theorem says that the gate halts exactly when \(N\) is a power of two, equivalently \(m=1\). In the successful case \(m>1\) is odd.

Define the carry sequence through the first odd carry by
\[
t_0=x_0+c,\qquad
t_{i+1}=x_{i+1}+t_i/2\quad(0\le i<r).
\]
The divisions are integral because \(t_i\) is even for every \(i<r\). The recurrence is continued with \(x_i=0\) after the original stack ends. Unrolling gives
\[
t_i=\frac{c+\sum_{j=0}^{i}2^j x_j}{2^i},
\qquad t_r=m.
\]
In a successful gate, the output coefficients \(u_i=G(c,S)_i+1\) have the exact form
\[
u_i=t_i/2\ (i<r),\qquad
u_r=(t_r+5)/2,\qquad
u_{r+1}=x_{r+1}+(t_r-1)/2,
\]
with \(u_i=x_i\) for \(i\ge r+2\). The convention \(x_i=0\) for \(i\ge n\) makes this one formula cover both a carry that stops inside the stack and a carry that drains beyond its end. The case \(m=1\) would require \(u_{r+1}=0\), corresponding to a tape digit \(-1\), and is precisely the halting case.

## 2. Exact generating-function identity

**Theorem (gate carry-polynomial identity).** For every successful gate transition \(G(c,S)=U\), with the carry sequence above,
\[
\boxed{
2\bigl(P_U(z)-P_S(z)\bigr)
=
2c+(z-1)\sum_{i=0}^{r}t_i z^i+5z^r-z^{r+1}.
}
\]
This is an identity in \(\mathbb Z[z]\).

*Proof.* At each position \(i<r\), the emitted coefficient is \(t_i/2\). The recurrence gives \(x_i=t_i-t_{i-1}/2\) for \(i\ge1\). At the first odd carry, the two emitted coefficients are \((t_r+5)/2\) and \(x_{r+1}+(t_r-1)/2\); the unchanged tail cancels from \(P_U-P_S\). Therefore
\[
\begin{aligned}
2(P_U-P_S)
={}&2c-t_0
+\sum_{i=1}^{r-1}z^i(t_{i-1}-t_i)\\
&+z^r(-t_r+t_{r-1}+5)+z^{r+1}(t_r-1),
\end{aligned}
\]
where the \(r=0\) case is read directly from the final pair. Collecting the coefficient of each \(t_i\) gives \((z-1)z^i\), and the remaining terms are \(2c+5z^r-z^{r+1}\). ∎

Several exact consequences follow immediately.

- At \(z=1\), \(M(U)-M(S)=c+2\), recovering the existing Lean theorem **G_mass**.
- Differentiating once at \(z=1\) gives the new positional-moment update
  \[
  \boxed{2(D(U)-D(S))=\sum_{i=0}^{r}t_i+4r-1.}
  \]
- More generally, for the falling-factorial moments
  \[
  M_k^{\downarrow}(S)=\sum_i (i)_{\underline{k}}x_i
  \]
  and every \(k\ge1\),
  \[
  \boxed{
  2\bigl(M_k^{\downarrow}(U)-M_k^{\downarrow}(S)\bigr)
  =
  k\sum_{i=0}^{r}(i)_{\underline{k-1}}t_i
  +5(r)_{\underline{k}}-(r+1)_{\underline{k}}.
  }
  \]
  Thus the gate has an exact hierarchy of moment-transfer identities, not only the unweighted mass law.

The first-moment formula is particularly useful because \(D\) is a statistic of the **whole** stack. A fixed prefix and total mass do not determine it.

## 3. Convex tail interval from prefix, mass, and positional moment

Suppose the stack length \(n\), its first \(k\) coefficients \(x_0,\ldots,x_{k-1}\), total mass \(M\), and positional moment \(D\) are known. Let \(L=n-k\ge2\), and define the residual tail mass and local first moment by
\[
R=M-\sum_{i<k}x_i,\qquad
J=D-\sum_{i<k}i x_i-kR.
\]
Subtract the mandatory one unit in each tail position:
\[
R_0=R-L,\qquad J_0=J-\frac{L(L-1)}2.
\]
Then \(z_j=x_{k+j}-1\) are nonnegative integers satisfying
\[
\sum_{j=0}^{L-1}z_j=R_0,\qquad
\sum_{j=0}^{L-1}jz_j=J_0.
\]
The unknown tail contribution to \(W\) is
\[
2^k\left(2^L-1+\sum_{j=0}^{L-1}2^jz_j\right).
\]

If \(R_0=0\), the tail weight is fixed. Otherwise let
\[
a=\left\lfloor J_0/R_0\right\rfloor,\qquad s=J_0-aR_0.
\]
Convexity of \(2^j\) gives the rigorous bounds
\[
T_{\min}=2^a(R_0+s)
\le \sum_j2^jz_j
\le
R_0+\frac{J_0}{L-1}(2^{L-1}-1)=T_{\max}.
\]
For the lower bound, the supporting line through \((a,2^a)\) and \((a+1,2^{a+1})\) lies below every point \((j,2^j)\). For the upper bound, the chord joining \((0,1)\) and \((L-1,2^{L-1})\) lies above the graph on the whole interval. Since the sum is integral, use \(\lfloor T_{\max}\rfloor\) for an integer upper bound.

Writing \(W_{\rm pre}=\sum_{i<k}2^i x_i\), this yields
\[
\begin{aligned}
W_{\min}&=W_{\rm pre}+2^k(2^L-1+T_{\min}),\\
W_{\max}&=W_{\rm pre}+2^k(2^L-1+\lfloor T_{\max}\rfloor).
\end{aligned}
\]
Every stack with the prescribed prefix, mass, length, and first moment has \(W_{\min}\le W(S)\le W_{\max}\).

For a candidate full-prefix carry, \(q=(W(S)+c)/2^{n-1}\) is an integer. Hence it must lie in
\[
\boxed{
\left\lceil\frac{W_{\min}+c}{2^{n-1}}\right\rceil
\le q\le
\left\lfloor\frac{W_{\max}+c}{2^{n-1}}\right\rfloor.
}
\]
If this integer interval contains no power of two, the gate cannot halt. This is a sound necessary-range test; it does not assume a model for the unknown tail.

## 4. Finite S4 trace examples

The following exact-integer examples use states from the finite source-shaped simulation rooted at the source-certified return-5457 state. The later states and interval calculations are computational, not Lean-kernel-certified.

| Trace state / gate | \(n\) | Known prefix \(k\) | \(c\) | \(M\) | \(D\) | Actual \(q\) | Moment-bounded \(q\)-interval |
|---|---:|---:|---:|---:|---:|---:|---:|
| return 5774, \(G_{509}\) | 18 | 13 | 509 | 5,914,823 | 72,146,379 | 349,592 | [299,056, 474,434] |
| first full-suffix event, \(G_{219}\) | 18 | 15 | 219 | 31,892,458 | 454,971,535 | 6,578,056 | [6,569,273, 7,029,452] |
| second full-suffix event, \(G_{290}\) | 22 | 18 | 290 | 957,270,726 | 18,038,129,200 | 283,561,618 | [270,817,160, 416,050,215] |

None of the three intervals contains a power of two. For the two full-suffix events, this excludes a terminal power gate without needing the exact terminal quotient's odd part.

The return-5774 example is also a useful separation from the earlier mass/shape obstruction. The known synthetic halter has \(W+c=2^{34}\), hence \(q=2^{17}=131,072\). It shares the older nine-digit prefix, full-stack mass, length, and final two digit values of the authentic simulated state. The stronger summary using the authentic first 13 coefficients, \(M\), and \(D\) gives the interval [299,056, 474,434], which excludes that synthetic halter. This does not show that the moment summary is globally invariant; it shows that it retains root-history information lost by the earlier coarse summary.

## 5. What remains to prove

The carry-polynomial identity and convex interval lemma are general exact mathematics. The examples show that the first positional moment can materially sharpen the terminal-quotient test. The missing step is a **root-reachable return law for \(D\)** (or a sufficiently tight interval for \(D\)) under the existing Q/R/V/W/X/Y/Z/F suffix words.

The update
\[
2\Delta D=\sum_{i=0}^{r}t_i+4r-1
\]
expresses the change through the carry polynomial at \(z=1\). The next productive target is to accumulate or bound this quantity across a return word, using its already-extracted prefix phases, and then apply the convex tail interval at the remaining candidate gates. If this closes, it would turn the finite 386/703 candidate-phase lists into a root-history-sensitive obstruction without merely extending the prefix depth again.

**Verification boundary:** the algebraic identities and convexity proof are given here on paper; no new Lean module has been compiled. The prescribed local shell/Python tool boundary returned only "Skipped 1 message" with no stdout or exit status on preflight, matching the previously recorded environment blocker. Per the repository rule, no CI run was substituted for the unavailable local Lean preflight. This note is intermediate work in im-results/, not a claim of a publishable BB(6) solution.
