# Uniform Cantor-resonance hierarchy: strict #429 signed prehistories with limiting coefficient 19/5

**Mathematical result and scope.** The following fully quantified **paper construction** produces source-aligned signed q0 macro paths with one-sided strict predecessor length at least \((19/5-o(1))k\) on a sequence of coefficient-two near-power centers. This sharpens the earlier [2190/583 fixed-triple construction](LongPastCascade.md) to a **two-level limit over arbitrary multiple-of-three reset lengths**. The uniform argument below is mathematical, not yet translated into an accepted Lean theorem. Independent finite exact-integer/source-macro replay exists for the \(M=3\) subfamily; the arbitrary-M integer parameter/carry inequalities can be reproduced with [long_past_uniform_m.cjs](long_past_uniform_m.cjs), which never constructs the astronomical \(4^k\).

**Crucial limitation:** These are synthetic paths in the exact signed halfstep/macro graph, **not** authentic blank #429 trajectories. No two-sided wide crossing, #429 holdout resolution, or BB(6) upper bound follows. The known wide radius grows like \(4^k/k\), much faster than the \(\Theta(k)\) histories here.

## The theorem

Choose any integer \(t\ge1\) and let \(M=3t\ge3\), \(\Lambda=4^M-1\), and \(\varepsilon=M\bmod2\in\{0,1\}\). As \(M\) is divisible by three, \(9\mid\Lambda\). Define the fixed integer
\[
 \beta_M=\frac{(24-3M-2\varepsilon)\,\Lambda/3-2M-\varepsilon}{2}.
\]
Choose **any even** integer \(s\ge M+1\), and set
\[
 R=s+2M,\qquad B_s=\frac{2\Lambda^2}{9}4^s-\frac{\Lambda s}{2}+\beta_M.
\]
Let \(\rho\) be the least nonnegative residue
\[
 \rho\equiv \beta_M-4^{R-1}\pmod{\Lambda}.
\]
Write \(\rho=\sum_{j=0}^{M-1}c_j4^j\) in exactly M base-four digits (leading zeros allowed), where each \(c_j\in\{0,1,2,3\}\), and form the **binary-base-four** correction
\[
 F=\sum_{j=0}^{M-1}\ \sum_{u=0}^{c_j-1}4^{j+uM},\qquad
 D=4^{R-1}+F.
\]
The empty inner sum for \(c_j=0\) is zero. All base-four digits of D are 0 or 1, and its leading 1 is at exponent \(R-1\). Define
\[
 h=\frac{2(D-B_s)}{\Lambda},\quad
 m=3+\frac{2\Lambda}{9}4^s,\quad
 k=m+1+h,\quad T=4^k,\quad
 q_f=k-2R-100M.
\]
Then \(h>0\) is an **even integer**, m is odd, k is even, \(q_f>0\), and the following **reverse-chronological** exact signed halfstep word is valid and strictly interior at every position, starting from
\[
 (P,Y)=(2T+4,\;2\cdot4^h):
\]
\[
\boxed{
0^m\,1\,0^{k-M-s}\,1^M\,0^{k-R}\,
\beta_R(D)\,0^{q_f},
}
\]
where \(\beta_R(D)\) denotes the R base-four digits of D, read from most to least significant. All even/A-rank states have even ordinate, and the word length
\[
\boxed{N=m+3k-3s-104M+1}
\]
is even. Pairing the chronological halfsteps therefore yields a legitimate original **radix-16 q0 signed macro path** of \(N/2\) transitions ending at \((4^k+2,4^h)\).

For each **fixed M**, as even s tends to infinity,
\[
\lim\frac Nk
 =3+\alpha_M,\qquad
\alpha_M=\frac{\Lambda^2}{9\cdot4^{2M-1}-\Lambda^2}.
\]
Taking M through the positive multiples of three yields \(\alpha_M\to4/5\). Consequently, if \(D_{\rm rev}(P,Y)\) is the maximal number of strict signed halfstep predecessors of a fixed positive-cone center, then
\[
\boxed{\displaystyle
\limsup_{k\to\infty}\ 
\max_{\substack{Y\in\mathbb N\\0<3Y<2\cdot4^k+4}}
\frac{D_{\rm rev}(2\cdot4^k+4,Y)}{k}
\ \ge\ \frac{19}{5}=3.8.
}
\]
More concretely, **for every \(c<19/5\)** there are infinitely many center ranks \(2\cdot4^k+4\) and exact aligned center heights for which a strict reverse history exceeds \(ck\) steps. This disproves every purported universal one-sided cutoff with coefficient \(c<3.8\). It does not preclude still longer histories.

## Modular encoding and positivity

Because \(4^M\equiv1\pmod\Lambda\), each term \(4^{j+uM}\equiv4^j\), so \(F\equiv\sum c_j4^j=\rho\pmod\Lambda\). Therefore
\[
 D=4^{R-1}+F\equiv \beta_M\equiv B_s\pmod\Lambda
\]
(the last congruence follows since \(2\Lambda^2/9\) is divisible by \(\Lambda\) and s is even). Thus h is even and integral. The exponents of the 1-bits in F are strictly below \(3M\); by \(s\ge M+1\), the leading exponent \(R-1=s+2M-1\) is at least \(3M\), so F and the leading power cannot overlap or introduce base-four carries. Accordingly
\[
 4^{R-1}\le D\le(4^R-1)/3.
\]

For positivity, note the strict rational inequality
\[
 A_M:=4^{2M-1}-\frac{2\Lambda^2}{9}
 \ge \frac{4^{2M}}{36}>0.
\]
Hence
\[
 D-B_s=A_M4^s+F+\frac{\Lambda s}{2}-\beta_M>0
\]
for \(M\ge3,s\ge M+1\). A completely explicit comparison follows from \(|\beta_M|\le(M+5)\Lambda\) and \(4^{2M+s}/36>(M+5)\Lambda\) throughout that domain. Likewise \(B_s>0\): the dominant \((2\Lambda^2/9)4^s\) term exceeds \((\Lambda s/2)+|\beta_M|\). The elementary bounds
\[
 k<4^R,\qquad k>4R+100M,\qquad R\le k/16
\]
follow from \(m\asymp(2/9)4^{s+M}\), \(0<h<2D/\Lambda<4^{s+M}\), and \(s\ge M+1\); the smallest admissible case \(M=3,s=4\) already has \(k=4744,R=10\), and the exponential margin grows with either parameter. In particular
\[
 T=4^k>100k\,4^{2R}.
\]
These very loose bounds make all strict-cone comparisons below uniform.

## The first exact cancellation: M consecutive inverse ones

Let \(r=k-M-s\). It has parity \(\varepsilon\) because k and s are even. Starting at \((2T+4,2\cdot4^h)\), the first \(m\) inverse zeros take the height exactly to \(T/2\), since \(m+h=k-1\). Because m is odd, the subsequent inverse one has cost 9 and offset 12; its height is
\[
 3m-9=\frac{2\Lambda}{3}4^s>0.
\]
After \(r\) more inverse zeros the height is
\[
 y_0=\frac{2\Lambda}{3}4^{s+r}
     =\frac{2T}{3}(1-4^{-M}),
\]
and the rank is \(p_0=2T-\delta\) for
\[
 \delta=3(m+r)+3-2\varepsilon
       =6m+6+3h-3M-3s-2\varepsilon.
\]

For the ensuing \(M\) inverse ones, write \(C_i\) for the accumulated rank loss through one i and \(c_i\in\{4,12\}\) for its phase-dependent height offset. The cost pattern alternates 3,9 or 9,3, depending on ε; \(C_M=6M+3\varepsilon\). Exact unwinding gives, after j of these ones,
\[
 y_j=\frac{2T}{3}(1-4^{j-M})+E_j,\qquad
 E_j=\sum_{i=1}^{j}4^{j-i}(\delta+C_i-c_i).
\]
All summands are strictly positive because \(\delta>12\). In particular at \(j=M\) the leading T term **vanishes exactly**. The finite weighted phase-cost sum is
\[
 K_M:=\sum_{i=1}^{M}4^{M-i}(C_i-c_i)
    =-2M-\varepsilon.
\]
This identity is proved directly by the alternating-cost equations: the bases \(K_1=-3,K_2=-4\) hold, and appending two more one-steps to either parity preserves the formula \(K_{M+2}=-2(M+2)-\varepsilon\) (the new weighted terms have costs \(6M+O(1)\) which cancel the \(16K_M\) term).

Consequently, with \(\Lambda=4^M-1\),
\[
\begin{aligned}
H:=y_M
 &=\frac{\Lambda}{3}\,\delta-2M-\varepsilon\\
 &=\frac{4\Lambda^2}{9}4^s+\Lambda h-\Lambda s
    +\frac{(24-3M-2\varepsilon)\Lambda}{3}-2M-\varepsilon\\
 &=\Lambda h+2B_s
 =\boxed{2D}.
\end{aligned}
\]
This identity holds for **arbitrary** \(M=3t\), not only triple-one blocks. The next \(L=k-R\) inverse zeros raise H to \(2D4^{k-R}=(2D/4^R)T\).

## The second cancellation: binary base-four digits

Starting from rank \(2T-\Delta\), where \(\Delta=\delta+(6M+3\varepsilon)+3L<10k\), and height \(2DT/4^R\), execute the R bits \(d_1,\ldots,d_R\) of \(\beta_R(D)\). Let \(\widehat C_i\le9i\) be their accumulated rank decreases, and \(\widehat c_i\in\{4,12\}\) the offset used for a one (zero has no offset). Every inverse step is one of the **exact original** signed halfstep transitions, with current rank parity determined by the alternating odd costs.

The exact integer identity after j bits is
\[
 y_j=2T\frac{D_{\mathrm{suffix},j}}{4^{R-j}}+
    \widehat E_j,\qquad
 \widehat E_j=\sum_{i=1}^j4^{j-i}
               d_i(\Delta+\widehat C_i-\widehat c_i),
\]
where \(D_{\mathrm{suffix},j}=\sum_{i=j+1}^R d_i4^{R-i}\). At \(j=R\) the suffix is zero: the large T term has **again cancelled exactly** and
\[
 0<y_R=\widehat E_R<4k4^R.
\]
The leading digit \(d_1=1\) guarantees positivity. Every retained suffix contains only 0 and 1 base-four digits, so \(D_{\mathrm{suffix},j}\le(4^{R-j}-1)/3\), and
\[
 3y_j<2T-2T4^{-R}+12k4^R
       <2T-36k.
\]
The final \(q_f=k-2R-100M>0\) zeros have endpoint height
\[
0<y_{\mathrm{final}}
  =\widehat E_R4^{q_f}
  <\frac{4k}{4^{R+100M}}T
  <\frac{T}{4^{100M-1}},
\]
also safely in the cone.

## Why all intermediate positions are strict and source-aligned

Every reverse rank decreases by a positive odd cost at most 9. The displayed path has length \(N<4k\), so **every** reverse rank exceeds \(2T-36k\). All heights are positive (the one-block error terms are positive and the binary-digit block begins with a 1).

The first zero block ends at \(T/2\), the second at \(y_0<2T/3\) with rank-cone margin at least \(2T4^{-M}>36k\). During the M-one block,
\[
0<E_j<(\delta+9M)\frac{4^j-1}{3},
\]
so \(3y_j<2T-2T4^{-M}+8k4^M<2T-36k\) using \(T>100k4^{2R}\) and \(R\ge M\). The next zero block ends at \(2DT/4^R<2T/3-2T/(3\cdot4^R)\), again with a large margin. All binary-digit stages satisfy the bound in the preceding section, since the error is at most \(4k4^R\). The final zero block has the small height bound above. **Inside any zero run**, height increases with reverse time and rank decreases; verifying the last state therefore verifies every earlier state. This completes strictness at every vertex, not only the checkpoints.

All ranks change parity at every inverse step. A reverse zero produces a multiple of four. A reverse one that ends at an even rank q has ordinate \(4y-q-12\), which is automatically even. The initial center rank and height are both even. Therefore the correct even/A-height parity guard holds throughout, and the even N halfsteps pair into the **unchanged** q0 signed radix-16 macro map (digits 0,1,4,5; costs 3,5,4,6; offsets 0,6,18,32). This is no parity-relaxed, rational, or artificially pruned graph.

## The 19/5 limit and reproducible checks

For fixed M, let s increase through even integers. The bounded correction F is independent of s except for its residue class mod M and always satisfies \(F<4^{3M}\), so
\[
 m\sim\frac{2\Lambda}{9}4^s,\qquad
 h\sim\frac{2}{\Lambda}\left(4^{2M-1}-\frac{2\Lambda^2}{9}\right)4^s.
\]
Thus \(N/k\to3+\Lambda^2/(9\cdot4^{2M-1}-\Lambda^2)\). Writing \(X=4^M\), this extra coefficient equals
\[
 \frac{(X-1)^2}{\frac94 X^2-(X-1)^2}
 \longrightarrow\frac45
 \quad(M\to\infty).
\]
The two limits are taken in this order; the \(\limsup\) lower bound follows by choosing M first, then infinitely many sufficiently large even s.

| M | fixed-M limit for N/k | illustrative (M,s) | k | length N |
| ---: | ---: | --- | ---: | ---: |
| 3 | 3.756432247 | (3,4) | 4,744 | 17,496 |
| 6 | 3.799297235 | (6,10) | 1,204,426,070 | 4,567,481,720 |
| 9 | 3.799989014 | (9,10) | 76,355,775,154 | 290,151,070,804 |
| 12 | 3.799999828 | (12,14) | 1,438,649,549,149,524 | 5,316,748,504,988,406 |

The large numeric rows are **symbolic integer certificates**, not executed step-by-step histories across astronomical tape/rank sizes. [long_past_uniform_m.cjs](long_past_uniform_m.cjs) constructs the modular binary digit word, verifies exact cancellation after arbitrary M ones and arbitrary R bits using affine-in-\(4^k\) coefficients, and checks the sufficient cone bounds **without ever materializing \(T=4^k\)**. Reproduce:

~~~sh
node im-results/agent18-429-odd-macro/long_past_uniform_m.cjs
node im-results/agent18-429-odd-macro/long_past_uniform_m.cjs 6 10
~~~

For the \(M=3\) subfamily, [long_past_cascade.cjs](long_past_cascade.cjs) independently replays **every source-macro nonzero transition**, exact divisibility of zero blocks, and full halfstep phase guards at \(k\) as high as 1,213,076; this is the source-level reproducibility check that complements the all-M symbolic calculation.

## What remains open

This is a **rigorous paper-level construction** inside the signed #429 macro model. The source model and finite simulations have separately existing Lean theorems; the **new unbounded quantified parametrization itself does not yet have a Lean source-closure proof**, so do not promote it as a formally verified theorem. More importantly, it offers no connection from the real blank machine to these synthetic entrance states and supplies only a long past, not the exponentially longer *two-sided* wide window sought by the outstanding noCross hypothesis. One possible next research direction is to iterate the modular Cantor-carry construction further to decide whether the normalized inverse-depth limsup is finite or unbounded; neither possibility follows from this theorem.
