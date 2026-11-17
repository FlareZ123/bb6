# Exact 3-adic valuation normal form for the source drain

**Status:** mathematically derived from the unchanged source evaluator and drain; the one-step evaluator lemma is drafted in **DrainValuationNormalForm.lean** but still needs CI compilation and axiom audit. The full iterated-drain theorem below has an elementary induction proof sketched here; it is not yet a separate Lean theorem.

## 1. The evaluator is a 3-adic valuation step

Let \(b>0\), and set
\[
v=\nu_3(2b-1),\qquad u=(2b-1)/3^v.
\]
The integer \(u\) is odd and not divisible by 3, so \(u\equiv1\) or \(5\pmod6\). Define
\[
\epsilon=\begin{cases}0&u\equiv1\pmod6,\\1&u\equiv5\pmod6,\end{cases}
\qquad
b^+=(u-1-4\epsilon)/6.
\]
Equivalently,
\[
b-1=\tau(v)+3^v(3b^++2\epsilon),
\qquad \tau(v)=(3^v-1)/2.
\]
In particular \(b^+<b\).

If \(a\ge v+1\), the unchanged source evaluator satisfies the exact identity
\[
\operatorname{evalA}(a,b-1,m)=
\left(
a-v-1+2\epsilon,\;
b^+,\;
m+(6b^++1+4\epsilon)\tau(v)+2v+2(1-\epsilon)
\right).
\tag{1}
\]

**Proof.** The base-three expansion of \(b-1\), read from the least significant digit, begins with exactly \(v\) copies of \(1\). The next digit is \(0\) when \(\epsilon=0\), and \(2\) when \(\epsilon=1\). Each low-order \(1\) invokes the recursive evaluator clause, decrementing the first counter and adding \(2\lfloor(b-1)/3^i\rfloor+3\) to the third counter. The next digit \(0\) decrements the first counter once more and adds 2; the next digit \(2\) increments the first counter and adds nothing. Summing the \(v\) recursive increments gives
\[
\sum_{i=1}^{v}\left(2\left\lfloor\frac{b-1}{3^i}\right\rfloor+3\right)
=(6b^++1+4\epsilon)\tau(v)+2v.
\]
This proves (1) by induction on \(v\). The Lean draft formalizes precisely this one-call statement, with the ternary decomposition as its hypothesis.

The factorization
\[
2b-1=3^v(6b^++1+4\epsilon)
\]
shows that \(v\) is exactly the 3-adic valuation, not merely a run-length proxy.

## 2. The whole drain is a valuation-cost cocycle

Starting from \(b_0=b\), repeatedly define
\[
v_i=\nu_3(2b_i-1),\quad
\epsilon_i\in\{0,1\},\quad
b_{i+1}=\frac{(2b_i-1)/3^{v_i}-1-4\epsilon_i}{6}.
\]
Stop at \(b_r=0\). This sequence is determined by \(b\) alone; the first and third counters do not affect it. The strict decrease \(b_{i+1}<b_i\) makes the process finite.

Define the signed valuation cost and length
\[
D(b)=\sum_{i=0}^{r-1}(v_i+1-2\epsilon_i),
\qquad R(b)=r.
\]
The cost is signed: a step with \(v_i=0,\epsilon_i=1\) contributes \(-1\).

At each step, (1) gives
\[
a_{i+1}=a_i-(v_i+1-2\epsilon_i)
\]
and, after including the next drain counter,
\[
d_{i+1}+3b_{i+1}
=d_i+3b_i+2(v_i+1-2\epsilon_i)+2.
\]
Summing over the drain yields the exact normal form, whenever the source ternary budget ensures all evaluator calls succeed:
\[
\boxed{
\operatorname{drainB}(a,b,d)
=
\bigl(a-D(b),\ d+3b+2D(b)+2R(b)\bigr).
}
\tag{2}
\]
The pair on the right denotes the two output counters. The existing source theorem **drainB_safe_ones** supplies totality under \(b\le\tau(a)\); the evaluator budget is preserved at each step. Thus (2) is an exact reformulation of the source drain, not an approximation or a new simulator.

### 2.1 A nonrecursive ternary-digit formula

The valuation word itself can be eliminated. Put
\[
s_0=0,\qquad s_{i+1}=s_i+v_i+1,\qquad
p_i=s_i+v_i,\qquad L=s_r,\qquad e=\sum_{i<r}\epsilon_i.
\]
For \(x_i=2b_i-1\), the one-step factorization gives
\[
x_i=3^{v_i+1}x_{i+1}+4(1+\epsilon_i)3^{v_i}.
\]
Unrolling to \(x_r=-1\) yields
\[
2b-1=4\sum_{i=0}^{r-1}(1+\epsilon_i)3^{p_i}-3^L,
\]
hence
\[
N=\frac{2b-1+3^L}{4}
=\sum_{i=0}^{r-1}(1+\epsilon_i)3^{p_i}.
\tag{3}
\]
The positions \(p_i\) are strictly increasing and the coefficients are \(1\) or \(2\). Thus (3) is exactly the ordinary base-three expansion of \(N\), with no carries:
- \(r\) is the number of nonzero ternary digits of \(N\);
- \(e\) is the number of ternary digits equal to \(2\);
- \(D=L-2e\).

The parity relation follows directly from the step decomposition:
\[
b_i\equiv b_{i+1}+v_i+1\pmod2,
\]
so \(L\equiv b\pmod2\). Since the top ternary digit of \(N\) is nonzero at position \(L-1\), one has \(3^{L-1}\le N<3^L\). Using \(2b-1=4N-3^L\) gives
\[
3^{L-1}\le2b-1<3^{L+1}.
\]
These inequalities and the parity condition uniquely determine \(L\): it is either \(\lfloor\log_3(2b-1)\rfloor\) or that integer plus one, whichever has the parity of \(b\).

Consequently the whole drain has the fully nonrecursive digit-statistic form
\[
\boxed{
\operatorname{drainB}(a,b,d)
=
\left(
a-L+2e,\;
d+3b+2L+2r-4e
\right),
}
\tag{4}
\]
under the same source ternary-budget condition. This is stronger than the valuation-cost form (2): \(L\) is a parity-adjusted logarithmic depth, while \(r\) and \(e\) are ordinary ternary Hamming-weight and digit-2 counts of the single explicit integer \(N=(2b-1+3^L)/4\).

The closed form was compared with the recursive valuation process for every \(1\le b\le100{,}000\), with zero discrepancies. This is computational corroboration; the proof is the unrolling identity (3).

## 3. Canonical-ray residuals become ordinary digit statistics

For the explicit integer \(N=N(b)\) in (3), let
\[
e=\#\{\text{ternary digits of }N\text{ equal to }2\},
\qquad
\Delta=\#\{\text{digits equal to }1\}-\#\{\text{digits equal to }2\}.
\]
If \(r\) is the ternary Hamming weight, then \(\Delta=r-2e\), while \(D=L-2e\). The drain formula (4) therefore simplifies to
\[
\boxed{
\operatorname{drainB}(a,b,d)
=
\bigl(a-L+2e,\ d+3b+2L+2\Delta\bigr).
}
\tag{5}
\]
Only three elementary statistics of \(N\) are needed: its depth \(L\), number of 2-digits \(e\), and signed digit count \(\Delta\).

For the four canonical ray families, write \(m=\min(a,d)\). Their base drain inputs are:

| Input ray | Base drain \((A,b,d_0)\) | First-coordinate shift |
|---|---|---:|
| left odd | \((k,m+3,5)\) | \(t\) |
| left even | \((k,m+2,2)\) | \(t\) |
| right odd | \((2k+5,m-1,3)\) | \(2t\) |
| right even | \((2k+3,m+1,0)\) | \(2t\) |

The right-even branch's initial evaluator followed by the drain is exactly the first iteration of
\[
\operatorname{drainB}(2k+3,m+1,0).
\]

The least integer exponent \(A_0(b)=\min\{a:b\le\tau(a)\}\) is also read off from \(N\):
\[
A_0(b)=L+\sigma,\qquad
\sigma=\begin{cases}0&N\le\tau(L),\\1&N>\tau(L).\end{cases}
\]
Indeed \(2b+1=4N-3^L+2\), and \(3^{L-1}\le N<3^L\) forces \(3^{L-1}<2b+1<3^{L+1}\). Thus \(A_0\in\{L,L+1\}\), with the threshold above deciding which. The right-ray base exponent is the least admissible odd exponent (at least 5 for right-odd and 3 for right-even) not below \(A_0\). So the canonical exponent itself is determined by \(L\), one ternary threshold bit, and a parity adjustment.

Let \((B,E)\) be the base drain output. In the notation of **GapScaleResidualSource.lean**, the residuals
\[
\beta=B-c-v_0,\qquad \delta=E-3m
\]
are now explicit digit statistics:

| Input ray | \(\beta\) | \(\delta\) |
|---|---:|---:|
| left odd | \(-L+2e-5\) | \(2L+2\Delta+14\) |
| left even | \(-L+2e-2\) | \(2L+2\Delta+8\) |
| right odd | \(4-L+2e\) | \(2L+2\Delta\) |
| right even | \(1-L+2e\) | \(2L+2\Delta+3\) |

Thus the canonical-ray correction is computed directly from the ordinary ternary digits of the single integer \(N(m+c)\), with the appropriate branch offset \(c\).

## 4. Exact gap/scale cocycle in digit coordinates

Let \(g=a-4d\) in a left-oriented state and \(g=d-4a\) in a right-oriented state, and \(m=\min(a,d)\). The source gap/scale update is:

- If the **output** is left-oriented:
  \[
  g'=g-9m+\beta-4\delta,\qquad m'=3m+\delta.
  \]
- If the **output** is right-oriented:
  \[
  g'=-4g-9m+\delta-4\beta,\qquad m'=3m+g+\beta.
  \]

Substitution gives the exact eight cases below. “Output left/right” refers to the source comparison of the two output counters, not the sign of \(g'\).

| Input ray | Output side | \(g'\) | \(m'\) |
|---|---|---|---|
| left odd | left | \(g-9m-9L+2e-8\Delta-61\) | \(3m+2L+2\Delta+14\) |
| left odd | right | \(-4g-9m+6L-8e+2\Delta+34\) | \(3m+g-L+2e-5\) |
| left even | left | \(g-9m-9L+2e-8\Delta-34\) | \(3m+2L+2\Delta+8\) |
| left even | right | \(-4g-9m+6L-8e+2\Delta+16\) | \(3m+g-L+2e-2\) |
| right odd | left | \(g-9m-9L+2e-8\Delta+4\) | \(3m+2L+2\Delta\) |
| right odd | right | \(-4g-9m+6L-8e+2\Delta-16\) | \(3m+g-L+2e+4\) |
| right even | left | \(g-9m-9L+2e-8\Delta-11\) | \(3m+2L+2\Delta+3\) |
| right even | right | \(-4g-9m+6L-8e+2\Delta-1\) | \(3m+g-L+2e+1\) |

This is an exact affine cocycle driven by the ternary depth, count of 2-digits, and signed digit count of \(N\). The eight cases were checked against 148 canonical root transitions in a finite BigInt reproduction; that scan is a sanity check, not the proof.

## 5. Why this matters for the blank-root problem

The root-history problem previously had a correction cocycle expressed through \((\beta,\delta)\), whose values were outputs of nested ternary recursion. Equation (2) identifies those corrections with a **valuation-cost/length pair** \((D,r)\). This is a finite-memory extension of the projective state \((g,m)\): every high-level transition is governed by the appropriate row above, with \(D,r\) computed by a deterministic 3-adic descent on its canonical drain input.

The remaining problem is now more sharply posed: control the valuation-cost sequence of the *actual blank-root itinerary* strongly enough to prove that its old-ray distance never enters the logarithmic terminal window (equivalently, establish the proposed 3-adic residue separation for every root state). This note does **not** prove that all-time invariant, decide machine #623, or determine BB(6).

## Reproduction and source dependencies

- Original evaluator and ternary-budget facts: **Parity623Source.lean** (theorems **evalA_ones_budget**, **drainB_safe_ones**, **twice_ones_add_one_eq_pow**).
- Exact gap/scale residual identities: **GapScaleResidualSource.lean**.
- Canonical-ray definitions: **CanonicalRayCocycleSource.lean**.
- Independent weighted drain identity: **ExactDrainCocycleSource.lean**.
- Lean one-step theorem draft: **DrainValuationNormalForm.lean**.

The evaluator identity was exhaustively checked for \(10{,}000\) positive \(b\)-values and four admissible \(a\)-values per \(b\). The whole-drain normal form was checked on more than \(15{,}000\) budgeted small inputs. These checks are only debugging evidence; the proof is the digit-run induction above plus the source budget theorem.
