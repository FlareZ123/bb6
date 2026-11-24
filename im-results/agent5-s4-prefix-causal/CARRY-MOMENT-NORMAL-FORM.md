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

Fix a positive gate offset \(c\), and write \(N=W(S)+c\) and \(r=v_2(N)\). Define the carry sequence through its first odd value by
\[
t_0=x_0+c,\qquad
t_{i+1}=x_{i+1}+t_i/2\quad(0\le i<r),
\]
where \(t_i\) is even for every \(i<r\), and use \(x_i=0\) after the original stack ends. Unrolling gives
\[
t_i=\frac{c+\sum_{j=0}^{i}2^j x_j}{2^i}.
\]
In particular, \(t_r\) is the **local terminal odd carry**.

It is important not to confuse \(t_r\) with the global odd quotient \(q=N/2^r\). The exact relation is
\[
q=t_r+\sum_{j=r+1}^{n-1}2^{j-r}x_j.
\]
Thus \(q=t_r\) only when no nonzero stack coefficient remains beyond \(r\); if \(r<n-1\), then \(q\ge t_r+2>1\). The source theorem says that the gate halts exactly when \(N\) is a power of two, equivalently \(q=1\). Therefore a halt is possible only after the carry has reached or passed the end of the stack, and then it occurs exactly when \(t_r=1\).

In a successful gate, the output coefficients \(u_i=G(c,S)_i+1\) have the exact form
\[
u_i=t_i/2\ (i<r),\qquad
u_r=(t_r+5)/2,\qquad
u_{r+1}=x_{r+1}+(t_r-1)/2,
\]
with \(u_i=x_i\) for \(i\ge r+2\). The convention \(x_i=0\) for \(i\ge n\) covers both a carry that stops inside the stack and one that drains beyond its end. In the halting case there is no remaining coefficient beyond \(r\), so \(t_r=1\) makes \(u_{r+1}=0\), corresponding to the blank-tape halting condition.

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

A further corollary is strict monotonicity of the first positional moment. If r=0, then t_0=x_0+c is odd and at least 3, so 2ΔD=t_0-1≥2. If r≥1, all t_i≥1, hence 2ΔD≥(r+1)+4r-1=5r and ΔD≥⌈5r/2⌉≥3. Therefore every successful positive-offset gate strictly increases D; every successful three-gate P return increases D by at least 3. If a known prefix forces at least r_0 initial even carries with r_0≥1, the stronger lower bound ΔD≥⌈5r_0/2⌉ follows without knowing the deeper suffix.

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

| Trace state / gate | \(n\) | Prefix \(k\) | \(c\) | \(M\) | \(D\) | Actual \(q\) | Mass-only interval | Mass + moment interval |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| return 5774, \(G_{509}\) | 18 | 13 | 509 | 5,914,823 | 72,146,379 | 349,592 | [235,282, 2,422,617] | [299,056, 474,434] |
| first full-suffix event, \(G_{219}\) | 18 | 15 | 219 | 31,892,458 | 454,971,535 | 6,578,056 | [5,648,913, 18,169,406] | [6,569,273, 7,029,452] |
| second full-suffix event, \(G_{290}\) | 22 | 18 | 290 | 957,270,726 | 18,038,129,200 | 283,561,618 | [108,322,778, 817,226,728] | [270,817,160, 416,050,215] |

The mass-only intervals still contain powers of two: four in the return-5774 case, two in the first full-suffix event, and three in the second. After adding the first positional moment \(D\), each interval still contains the actual quotient but contains **no** power of two. Thus \(D\) contributes genuine discriminatory information beyond prefix, length, and total mass in all three finite examples.

There is also a source-rooted lower return law for \(D\), requiring no suffix reconstruction. For a gate whose nine-digit prefix has \(v_2(W(\text{prefix})+c)<9\), the true carry depth and its \(D\)-increment are determined exactly by that prefix. If the prefix value is divisible by \(2^9\), the true carry depth is at least 9, and the moment identity gives the lower bound
\[
\Delta D\ge\frac{\sum_{i=0}^{8}t_i+36}{2}.
\]
Summing these per-gate lower bounds over the source-aligned 81,920-return nine-digit projection gives 754,974,720 = 9,216\cdot81,920, exactly nine times the period's mass drift. Tracking the residual after **each of the three gates**, not only at P-return boundaries, gives minimum -237,910 (phase 20,629, after gate 3) and maximum 385,701 (phase 26,422, after gate 3). From the source-certified return-5457 stack, \(M_0=5,590,215\) and \(D_0=66,584,055\), this yields, at **every surviving gate boundary** along the root,
\[
D_n\ge D_0+9,216n-237,910
\quad\Longrightarrow\quad
\boxed{D_n\ge 9M_n+16,034,210.}
\]
The exact finite sum and gate-boundary residual extrema are reproducible in [ninth_moment_drift.py](ninth_moment_drift.py). This is a genuine root-history lower bound, conditional on survival. It is not yet tight enough by itself to eliminate all terminal powers: the remaining task is an upper bound or tighter interval for \(D\), or a complementary tail functional.

## 5. Second positional moment and short-tail reconstruction

Let
\[
F_2(S)=\sum_i i(i-1)x_i=E_2(S)-D(S),
\qquad E_2(S)=\sum_i i^2x_i.
\]
The second derivative of the carry-polynomial identity gives
\[
\Delta F_2=\sum_{i=0}^{r}i t_i+2r^2-3r.
\]
Eliminating the carry sum with \(t_i=x_i+t_{i-1}/2\) gives the exact alternative
\[
\boxed{
\Delta F_2
=2\sum_{i=0}^{r} i x_i
+2\left(\sum_{i=0}^{r}x_i+c\right)
-(r+2)t_r+2r^2-3r.
}
\]
For a full-stack carry, the two input sums are \(D\) and \(M\), and \(t_r\) is the odd part of the terminal quotient. This identity makes the second moment a natural companion to \(D\), although no all-time second-moment bound has yet been derived.

There is a particularly simple exact tail fibre when only four coefficients remain after a known prefix. Let \(z_j=x_{k+j}-1\ge0\), \(0\le j<4\), and let
\[
R=\sum z_j,\qquad J=\sum jz_j,\qquad K=\sum j^2z_j.
\]
Put \(A=(K-J)/2\) and \(t=z_3\). Then every feasible integer tail, and only such a tail, has
\[
z_2=A-3t,\qquad z_1=J-2A+3t,\qquad z_0=R-J+A-t,
\]
with
\[
\max\!\left(0,\left\lceil\frac{2A-J}{3}\right\rceil\right)
\le t\le
\min\!\left(\left\lfloor\frac A3\right\rfloor,R-J+A\right).
\]
Its weighted excess is the affine function
\[
\sum_{j=0}^{3}2^jz_j=R+J+A+t.
\]
Thus the second moment turns the terminal quotient into an exact integer interval, rather than the much wider mass-only or first-moment convex envelope. For a three-digit tail, \(R,J,K\) determine all three coefficients uniquely:
\[
z_2=(K-J)/2,\quad z_1=2J-K,\quad z_0=R+(K-3J)/2.
\]

The finite S4 root replay gives two concrete checks. At the first full-suffix event (relative return 25,685, \(G(219)\)), the three-digit tail is reconstructed exactly as \((13,047,686,3,611,172,35,134)\), with quotient \(6,578,056\). At the second event (relative return 929,375, \(G(290)\)), the four-digit moment fibre gives
\[
283,510,228\le q\le296,203,294,
\]
which excludes all powers of two and contains the replayed quotient \(283,561,618\). The reproducible exact-integer computation is in [s5457_root_extension.mjs](../agent5-s4-nested-depth6/s5457_root_extension.mjs) and the event-level derivation is in [ROOT-EXTENSION-1310720.md](../agent5-s4-nested-depth6/ROOT-EXTENSION-1310720.md).

**Evidence boundary:** the tail-fibre inequalities are exact mathematics, but the particular \(E_2\) values and later root states are from finite BigInt simulation, not a Lean-certified all-time root invariant. This closes no future event and does not prove S4 nonhalting.

## 6. What remains to prove

The carry-polynomial identity and convex interval lemma are general exact mathematics. The examples show that the first positional moment can materially sharpen the terminal-quotient test. The missing step is a **tight root-reachable interval for \(D\)** under the existing Q/R/V/W/X/Y/Z/F suffix words: the nine-prefix cycle now supplies a uniform affine lower bound, but not a matching upper bound.

The update
\[
2\Delta D=\sum_{i=0}^{r}t_i+4r-1
\]
expresses the change through the carry polynomial at \(z=1\). The next productive target is to obtain a useful upper bound for the same carry-polynomial sum across a return word, using its already-extracted prefix phases, then apply the convex tail interval at the remaining candidate gates. The source-rooted lower bound is already available in ninth_moment_drift.py.

The same generating-function identity also gives a discounted potential
\[
Q(S)=P_S(1/2)=\sum_i x_i2^{-i}.
\]
Using \(t_i=x_i+t_{i-1}/2\) with \(t_{-1}=2c\), put \(T(1/2)=\sum_{i=0}^{r}t_i2^{-i}\). Summing the recurrence gives
\[
T(1/2)=\frac43\left(P_{\le r}(1/2)+c-\frac{t_r}{2^{r+2}}\right).
\]
Substitution into the generating-function identity yields the corrected exact formula
\[
\boxed{\Delta Q=\frac{2c-P_{\le r}(1/2)}3+\frac{t_r+27}{3\cdot2^{r+2}}.}
\]
In particular, if the carry passes the entire current stack, then \(P_{\le r}(1/2)=Q(S)\) and
\[
Q(U)=\frac23Q(S)+\frac23c+\frac{t_r+27}{3\cdot2^{r+2}}.
\]
More generally, for \(r\ge k\), write \(Q_{>r}=\sum_{i>r}x_i2^{-i}\). Then
\[
Q(U)=\frac23Q(S)+\frac23c+\eta,\qquad
\eta=\frac13Q_{>r}+\frac{t_r+27}{3\cdot2^{r+2}},
\]
and \(0\le\eta\le(3M(S)+c+27)/(3\cdot2^{k+2})\), using \(Q_{>r}\le M(S)/2^{r+1}\) and \(t_r\le M(S)+c\). Thus the correct long-carry contraction factor is **\(2/3\), not \(1/2\)**. The earlier half-contraction formula was an algebraic error and must not be used. Carries stopping inside the known prefix still have an exact update.

There is also a complementary tail bound from Q. For the tail excesses z_j=x_{k+j}-1, let R_0=Σz_j and Q_0=Σ2^{-j}z_j. Cauchy-Schwarz and the endpoint chord for 1/y on y∈[2^{-(L-1)},1] give
\[
\frac{R_0^2}{Q_0}\le\sum_j2^jz_j
\le R_0+2^{L-1}(R_0-Q_0).
\]
This turns a sufficiently tight interval for Q into another interval for W. Exact-Q finite checks give q intervals [6,163,349, 7,480,849] at the first full-suffix event and [229,282,800, 549,298,395] at the second; the first excludes powers of two, while the second does not.

A finite root-propagation of the **corrected** \(2/3\) recurrence through the 18-digit prefix, from the seed to the second event (relative return 929,375, before \(G(290)\)), is too coarse by itself. It yields the outward-rounded tail-excess interval
\[
175,849,077\le Q_0=\sum_{j=0}^{3}2^{-j}z_j\le702,151,658,
\]
and the Cauchy-Schwarz/chord bounds then give
\[
123,903,222\le q\le742,649,644.
\]
This still contains \(2^{27},2^{28},2^{29}\). The exact-Q interval above is substantially narrower, but requires the full finite stack. Thus the corrected Q recurrence is algebraically valid, but the straightforward 18-prefix interval propagation is **not** a decisive obstruction; it needs a sharper bound on the carry remainder or a joint moment argument. This finite diagnostic is recorded to avoid repeating the same coarse propagation; it is reproducible with [s4_q_prefix_interval.mjs](s4_q_prefix_interval.mjs).

**Verification boundary:** the algebraic identities and convexity proof are given here on paper; no new Lean module has been compiled. The prescribed local shell/Python tool boundary returned only "Skipped 1 message" with no stdout or exit status on preflight, matching the previously recorded environment blocker. Per the repository rule, no CI run was substituted for the unavailable local Lean preflight. This note is intermediate work in im-results/, not a claim of a publishable BB(6) solution.
