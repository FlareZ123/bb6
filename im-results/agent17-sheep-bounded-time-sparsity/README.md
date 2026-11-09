# Quantitative finite-time scarcity of Sheep halting starts

**9 November 2026; mathematical paper proof with exact finite-code checks, not Lean-kernel checked.** The authentic Sheep section's exceptional and terminal states have natural density **exponentially small in binary precision** among initial positive even integers whose first `n` even returns encounter either event, provided `n` is any fixed fraction smaller than one quarter of the input bit length. This strengthens the earlier square-root-logarithmic bound substantially. It follows from the exact *generic* dyadic branch coding of Agent22 combined with the **actual source's** strict increase and exceptional-state classification. The mathematical claim applies to varying source integers. It establishes no all-time nonhalting result for the single blank-origin entry `10`, no BB(6) decision, and no external academic novelty.

## Definition and strongest theorem

For even integers `x>=10`, write `x=2^a u`, `a>=1`, `u` odd. The original Sheep section halts precisely when `u=1`. Otherwise its next ordinary section value is
[
F(x)=\begin{cases}
x+a+3,&u=3,\\
x+a+(u-1)/2,&u\ge5.
\end{cases}
]
Factor `F(x)-1=2^h q` with `q` odd; its first following even section value is `E(x)=1+3^h q`. The **authentic original six-state source semantics**, strict increase `E(x)>x`, and the all-time blank-entry equivalence have already been Lean certified in [Agent16's source bridge](../agent16-sheep-even-return/README.md), [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547). The present argument starts at an *arbitrary* even positive integer, which need not be blank-reachable.

For `p>=3`, let `H(p,n)` be the number of even `x` with `10<=x<=2^p` whose actual path **first reaches a halting power `2^a` within at most `n` successful even returns**, including `n=0`. Fix integers `2<=r<p`, set `R=r-1`, `m=p-R=p-r+1`, and let
[
B(m,n)=\begin{cases}
0,&n=0,\\
2^{-m}\displaystyle\sum_{j=0}^{\min(m,2n-1)}\binom mj,&n\ge1.
\end{cases}
]

**Exact finite-modulus upper bound (all `p,n,r` in scope):**
[
\boxed{\frac{H(p,n)}{2^{p-1}}\le
2^{r-p}+(n+1)\left(2^{2-r}+B(p-r+1,n)\right).}\tag{1}
]

The right side may exceed one for small `p`, which is harmless. For every fixed real `0<\delta<1/4`, the choice `n=\lfloor\delta p\rfloor` and `r=\lfloor\varepsilon p\rfloor` with any fixed `0<\varepsilon<1-4\delta` gives
[
\boxed{H(p,\lfloor\delta p\rfloor)\le 2^{(1-\eta)p}}
\quad\text{for every sufficiently large }p
\tag{2}
]
for some `eta>0` depending only on `delta,epsilon`. Thus **the fraction halting within any `delta*log_2 N` first-even returns tends to zero for every `delta<1/4`**, uniformly over all even starts `x<=N`, including non-dyadic cutoffs `N`. Equivalently, asymptotically almost all even starts survive at least `floor(delta*log_2 N)` returns. The established stronger exceptional-inclusive bound applies to *first visits* to either odd cofactor `1` or `3`.

An explicit **near-one-quarter horizon** is also available. Write `p` for the bit budget and, for sufficiently large `p`, choose
[
r=\lceil3\log_2 p\rceil+3,\qquad
n=\left\lfloor\frac p4-2\sqrt{p\log_2 p}\right\rfloor.
]
Then the same exact bound (1) gives
[
\boxed{H(p,n)\,/\,2^{p-1}=O(p^{-2}).}\tag{2b}
]
The survival horizon therefore approaches **one quarter of the input bit length**, with a sublinear `O(sqrt(p log p))` correction, while the fraction of exceptions tends to zero. The explicit proof is in §4 below.

These are natural-density, **integer-source** conclusions with growing horizons. They are substantially stronger than the earlier Haar-almost-everywhere theorem alone, because Haar-null countable sets of ordinary integers can have positive natural density. The fixed integer `10` remains undecided.

## Proof of the finite bound

**1. Exact generic branch code.** Define the auxiliary generic map `E_g` on every even positive integer by using the `u>=5` formula `F_g(x)=x+a+(u-1)/2` for *all* odd `u`, including `1` and `3`. Factor `F_g(x)-1=2^h q` and set `E_g(x)=1+3^h q`. This is a computational auxiliary: its behavior on the two exceptional odd cofactors differs from the original source. For all legal `u>=5` it agrees **exactly** with the authentic `E`.

For a generic step, the branch letter is `(a,h)`, with cost `c=a+h+1`. As established algebraically in [Agent22's complete dyadic code](../agent22-sheep-mixed-hub/DYADIC-COMPLETENESS.md) and [Bernoulli branch theorem](../agent22-sheep-2adic-bernoulli/README.md), each finite branch word `w` of length `i` and total cost `C` defines **one** even residue class modulo `2^(C+1)`. On that class, the composite generic map has the exact affine difference law
[
E_g^i(x+2^{C+1}t)=E_g^i(x)+2At
\qquad(A\text{ odd}).
\tag{3}
]
Consequently, for `C+R<=p`, among the `2^(p-1)` even residues modulo `2^p`, the cylinder contains `2^(p-C-1)` starts, and exactly `2^(p-C-R)` map to the prescribed even target residue `0 mod 2^R`. The cylinder's relative measure is `2^{-C}`.

The binary costs `a` and `h+1` are independent positive geometric variables with probability `2^{-k}` for `k>=1`. Equivalently, there are exactly `binom(C-1,2i-1)` length-`i` words of total cost `C` and each has relative frequency `2^{-C}`. Therefore the proportion of even input residues whose first `i` generic symbols cost more than `m` is **exactly**
[
\Pr(C_i>m)=2^{-m}\sum_{j=0}^{\min(m,2i-1)}\binom mj
\qquad(i\ge1).
\tag{4}
]
The right side is the lower tail of `Binomial(m,1/2)`: `C_i` is the wait for the `2i`-th success in a stream of fair bits. Formula (4) also follows by taking the complement of all finite word cylinders with total cost `<=m`; hence it is **exact for the finite set of positive even representatives modulo `2^p`** whenever `m+1<=p`. For `i=0`, define `C_0=0` and the tail is zero.

**2. A finite-precision target bound.** Fix `i<=n`, set `m=p-R`, and partition the `2^(p-1)` possible even residue representatives by `C_i<=m` or `C_i>m`. The second part has exact fraction `B(m,i)<=B(m,n)`. On the first part, equation (3) says each length-`i` cylinder maps uniformly onto even residues modulo `2^R`. Summing its cost-weighted fraction yields at most `2^{1-R}`: indeed `\sum_{w,\,C(w)<=m}2^{-C(w)}<=1`. Thus
[
\frac{\#\{x\text{ even mod }2^p:E_g^i(x)\equiv0\pmod{2^R}\}}
{2^{p-1}}\ \le\ 2^{1-R}+B(m,i)
\ \le\ 2^{2-r}+B(m,n).
\tag{5}
]
Where a symbolic 2-adic exceptional point makes a branch undefined, its finite positive representative still has the complete ordinary generic formula; the prefix-count argument uses only the finite residue cylinders, so no arbitrary infinite tail assignment is needed.

**3. Transport from generic coding to *actual* halting.** Separate the at most `2^(r-1)` even starting integers `x<2^r`, a fraction at most `2^{r-p}`. Take any other authentic initial `x_0>=2^r` that halts by return index `n`. Let `i` be the **first** index at which the odd cofactor of `x_i` is `1` or `3`. This index exists and satisfies `0<=i<=n`: a terminal power itself has cofactor `1`. For every `t<i`, the authentic step uses the generic branch, so `x_i=E_g^i(x_0)`. Strict increase along authentic returns gives `x_i>=x_0>=2^r`.

If `x_i=2^a`, then `a>=r`. If `x_i=3*2^a`, then `a>=r-1`, since `3*2^(r-2)<2^r`. Therefore **in either case**
[
E_g^i(x_0)=x_i\equiv0\pmod{2^{r-1}}.
\tag{6}
]
Union bound over `i=0,...,n`, invoke (5), and add the small starts to prove (1). This accounts explicitly for the **exceptional authentic `u=3` path** rather than incorrectly applying the generic dynamics after it.

**4. Linear and near-critical horizons.** Choose `n=floor(delta*p)`, `r=floor(epsilon*p)` with `0<epsilon<1-4delta`. Then `m=p-r+1=(1-epsilon)p+O(1)` and `2n/m<1/2` by a fixed margin. The standard elementary Chernoff bound for the fair-binomial lower tail gives `B(m,n)<=2^{-kappa*p}` for some `kappa>0`, while `2^{2-r}<=2^{-epsilon*p+O(1)}` and `2^{r-p}<=2^{-(1-epsilon)p+O(1)}`. Multiplication by `n+1=O(p)` preserves an exponentially small total fraction, proving (2).

For (2b), the proposed `r` is `3log_2 p+O(1)`, and `m=p-O(log p)`. Its fair-binomial mean is `m/2`. At the proposed `n`, the gap from the mean to the tail threshold obeys, for sufficiently large `p`,
[
\frac m2-(2n-1)\ge2\sqrt{p\log_2 p}.
]
Hoeffding's inequality bounds the binomial lower tail by
[
B(m,n)\le\exp\left(-\frac{2(2\sqrt{p\log_2 p})^2}{m}\right)
\le\exp(-8\log_2 p)\le p^{-3}
]
for large `p`. Also `2^{2-r}=O(p^{-3})`, `2^{r-p}=O(p^3 2^{-p})`, and `n+1=O(p)`. Substitution in (1) yields (3). For arbitrary `N`, choose `p=ceil(log_2 N)`; the dyadic interval contains all starts up to `N` and has at most twice as many even integers, so the same conclusions follow.

## Complementary elementary bound without symbolic coding

There is also an independent, weaker all-`N,n` bound obtained solely from the published first-even formula. For `N>=10`, define `alpha=log_2 3`, `L=ceil(log_2 N)+6`, and count halting starts `H_N(n)` in `[10,N]`. The following inequality holds for all `n>=0`:
[
\boxed{H_N(n)\le2(n+1)9^n\alpha^{n^2+2n}L^{2n+1}.}\tag{7}
]
Indeed `F(x)<=2x` and `E(x)-1=3^h q<=(2^h q)^alpha` imply `E(x)<=(4x)^alpha`. Iteration yields `log_2 x_i<=alpha^i L`. Put `J_i=ceil(alpha^i L)`; each terminal power at level `k` has at most `J_k` possible exponents, and every even target `y<=2^(J_i)` has at most `(J_i+1)^2` authentic direct parents. For generic sources this follows from
[
2(F(x)-1)=(1+2^{a+1})u+2a-3,
]
which determines at most one `u` for each pair `(a,h)` with `1<=a<=J_i`, `0<=h<=J_i`; exceptional `u=3` contributes at most `J_i` more. Backward multiplication gives `J_k\prod_{i=1}^k(J_i+1)^2<=2\cdot9^k\alpha^{k^2+2k}L^{2k+1}`; summing to `n` proves (7). It independently implies density zero for `n=c*sqrt(log_2 N)` with `c<1/sqrt(log_2 alpha)`, but (1) is much stronger.

The growth exponent `alpha` is optimal for a pointwise one-step polynomial growth bound: for every `h=4s+1>=5`, `u=(2^(h+1)+1)/5` is odd, and `x=2u` satisfies `F(x)-1=2^h`, `E(x)=1+3^h`. Consequently `log E(x)/log x\to alpha` along this family.

## Evidence, novelty, and exact missing BB(6) quantifier

The branch-cylinder laws and product cost distribution used in the main result have all-parameter **written mathematical proofs** in Agent22's two dossiers linked above, plus independent modular regressions; they are not claimed to be Lean-kernel-certified. The present argument supplies the new source-exception transport, exact finite-start bound, and linear-horizon density deduction. A small independent exact-code regression is in [finite_code_check.py](finite_code_check.py). This result is intermediate; it has not received external peer review. It does **not** imply the single original blank start `10` escapes its exceptional state at any untested time. No new BB(6) lower/upper bound or holdout decision follows.

For BB(6), the missing obligation is still a **pointwise, all-time** statement about the one authentic Sheep trajectory. Finite positive-density families of freely chosen starts or a natural-density-one survival theorem do not supply it. A future useful application would combine this quantitative branch coding with a source-derived invariant that narrows the *specific* root's admissible exceptional histories.
