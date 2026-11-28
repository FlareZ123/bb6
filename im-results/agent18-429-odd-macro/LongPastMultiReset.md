# Two-parameter unbounded maximal reverse histories at the fixed coefficient-two centers

**Mathematical statement (exact symbolic proof; not yet formally quantified in Lean).** Let \(t\ge1\), \(s\ge0\), and
\[
M=3t,\qquad A=\frac{4^M-1}{9}\in\mathbb N,\qquad
k=4+2A4^s,\qquad r=k-M-s,\qquad q=k-s-2M.
\]
Then \(k\) is even, \(k\ge18\), \(r,q>0\), and at the **fixed center**
\[
(P,Y)=(2\cdot4^k+4,\ 2)
\]
there is a **unique maximal strict-interior backward half-step history of exactly**
\[
\boxed{N=3k-2s-2M}
\]
moves. Its reverse-chronological digit word is
\[
\boxed{0^{k-1}\ 1\ 0^r\ 1^M\ 0^q}.
\]
Moreover every intermediate even-rank A-phase ordinate is even, and \(N\) is even, so grouping chronological bit pairs produces an **exact signed radix-16 q0 macro path** of \(N/2\) steps terminating at macro state \((4^k+2,1)\). This is a *synthetic graph prehistory*, not evidence that the actual blank #429 machine reaches its initial state. It is strictly **one-sided** and does not contradict the exponentially longer, two-sided wide-window exclusion conjecture.

This generalizes [LongPastGeometricFamily.md](LongPastGeometricFamily.md), its case \(M=3\). Unlike a fixed three-one reset, \(M\) may now grow without bound, so the number of consecutive 1 bits in the exact source-aligned history is unbounded. The asymptotic length remains \(N=(3-o(1))k\) along these families. For example \((M,s,k,N)=(3,0,18,48),(6,0,914,2730),(9,0,58258,174756)\).

## Why the tuning exists

The modulus condition \(M=3t\) guarantees \(4^M\equiv1\pmod9\), hence A is integral. It follows that
\[
3k-12=2\,\frac{4^M-1}{3}\,4^s.
\]
Start at \(P=2T+4,Y=2\) where \(T=4^k\). The first \(k-1\) reverse zeros land at \((2T-3k+9,T/2)\), and the next reverse one lands at
\[
(2T-3k,\ 3k-12) =
\left(2T-3k,\ \frac{2(4^M-1)}3\,4^s\right).
\]
Another \(r=k-M-s\) zeros reach height
\[
y_0=\frac{2(4^M-1)}3\cdot4^{k-M}
    =\frac{2T}{3}(1-4^{-M}).
\]
The rank there is \(p_0=2T-\delta\), where
\[
\delta=3k+C_0(r),\quad
 C_0(r)=3r-2[r\text{ odd}],\quad
6k-3(M+s)-2\le\delta\le6k.
\]

Now make \(M\) consecutive reverse-one steps. At the j-th step let \(C_j\) be the accumulated one-step rank loss, \(c_j\in\{4,12\}\) the inverse offset, and \(p_j=p_0-C_j\). Here \(3j\le C_j\le9j\) and each cost is odd. Direct unwinding gives the **exact integer identity**
\[
y_j=\frac{2T}{3}(1-4^{j-M})+E_j,\qquad
E_j=\sum_{i=1}^{j}4^{j-i}(\delta+C_i-c_i).
\]
At \(j=M\), the entire enormous \(T\)-term cancels. The residual height is
\[
H=E_M>0,\quad
(\delta-12)\frac{4^M-1}{3}
 \le H\le
(\delta+9M)\frac{4^M-1}{3}.
\]
One final zero run of length \(q=k-s-2M\) gives \(y_{\rm start}=H4^q\), and the word length simplifies to \(N=(k-1)+1+r+M+q=3k-2s-2M\).

## All-state strict-cone and exact lattice proof

Elementary estimates from \(A=(4^M-1)/9\), \(M\ge3\), and \(4^s\ge s+1\) yield
\[
 k\ge2(M+s)+7,\quad k\ge2M+12,\quad
 \frac{T}{4^M}=4^{k-M}\ge4096k.
\]
For the last inequality use \(k-M\ge k/2+6\), \(k\) even, and \(2^k\ge k\). Hence \(T\ge1024k\), and the entire path decreases rank by less than \(9N\le27k\); every vertex rank is at least \(2T-27k\).

The first zero run ends at height \(T/2\), safely below one third of the current rank. The first one ends at small positive height \(3k-12\). The next zero run ends at \(y_0\) just below \(2T/3\), with exact cone margin at least \(2T4^{-M}-27k>0\). In all zero runs intermediate heights are smaller and ranks larger than at their final vertex, so the final endpoint check covers the whole run.

For the \(M\)-one block, \(\delta-12\ge4k>0\) makes every term in \(E_j\) positive and ensures \(y_j>0\). Since
\[
0<E_j\le(6k+9M)\frac{4^j-1}{3}
\quad\text{and}\quad M\le k,
\]
the cone inequality follows uniformly from
\[
3y_j
\le 2T-2T\,4^{j-M}+(6k+9M)4^j
<2T-27k
\]
using \(T4^{-M}\ge4096k\). This holds even at j=M, where the main term is zero. Each inverse step is thus strictly interior and has positive integer height.

For the A-phase parity, all zeros produce heights divisible by 4, and the first isolated one lands at even rank with even ordinate \(2(4^M-1)4^s/3\). During the M-one block, the leading \(T\)-term in the formula for \(y_j\) is an even integer. Modulo two only the final term of \(E_j\) contributes, so \(y_j\equiv \delta+C_j-c_j\equiv p_j\pmod2\), since \(c_j\) is even and \(p_j=2T-\delta-C_j\). Thus **every even-rank state has even height**. The final zeros preserve this parity. Paired chronological halfsteps reproduce exactly the source-defined radix-16 macro digits \(0,1,4,5\), costs \(3,5,4,6\), and offsets \(0,6,18,32\).

## Exact terminality and uniqueness of the prehistory

The final rank is even. Total rank loss, obtained by summing alternating phase-dependent zero/one costs, is
\[
D=9k-3M-6s+
\begin{cases}
 5,&M\text{ odd},\ s\text{ even},\\
 3,&M\text{ odd},\ s\text{ odd},\\
 4,&M\text{ even},
\end{cases}
\quad\text{so}\quad 0<D\le9k.
\]
Thus \(p_{\rm start}=P-D\ge2T+4-9k\). To control \(y_{\rm start}=H4^q\) as a fraction of T, first note that
\[
\frac{y_{\rm start}}{T}
=\frac{H}{4^{s+2M}}.
\]
The H lower bound and \(\delta-12\ge4k\) imply
\[
 H>k4^M,\qquad
 \frac{y_{\rm start}}T>\frac{k}{4^{s+M}}
 \ge \frac{2}{9}(1-4^{-M})
 \ge\frac7{32}>\frac16.
\]
For \(M\ge6\), the upper bound gives
\[
\frac{y_{\rm start}}T
<\frac{2k+3M}{4^{s+M}}
\le\frac49+\frac{8+3M}{4^M}
\le\frac49+\frac{26}{4096}<0.451.
\]
For \(M=3\), the stronger exact formula from the prior note gives \(H\le2030\cdot4^s\), so \(y_{\rm start}/T\le2030/4096<1/2\). In either case \(y_{\rm start}<T/2\), and \(p_{\rm start}\ge2T+4-9k\) with \(T\ge1024k\) yields \(4y_{\rm start}<p_{\rm start}\). Also \(y_{\rm start}>T/6\) gives \(12y_{\rm start}>p_{\rm start}-1\).

At this even-rank endpoint, a reverse-zero ancestor would require \(12y<p-1\), while a reverse-one ancestor would require \(4y>p+1\). Both fail. These two inverse bands are disjoint for **all** ranks: zero requires \(y<p/12\) and one \(y>p/4\) up to small integer offsets. Thus the entire constructed inverse path is unique, and its depth \(N\) is **maximal at the specified center (P,2)**.

## Checkers and remaining obligations

[long_past_multi_reset.cjs](long_past_multi_reset.cjs) tests the two-parameter formulas with arbitrary-precision BigInt. It fast-forwards zero runs using their exact parity-dependent rank-cost sum, explicitly performs every one step, checks every segment's maximal strict height, every A-phase parity, final forbidden inverse-band, and the residual bound \(H>k4^M\). It covers \((M,s)=(3,0),(3,1),(6,0),(6,1),(9,0),(9,1)\), up to \(k=233{,}020\). The M=3 special case is also directly replayed step-by-step through every halfstep and independently through source radix-16 macros in [long_past_family.cjs](long_past_family.cjs).

~~~sh
node im-results/agent18-429-odd-macro/long_past_multi_reset.cjs
node im-results/agent18-429-odd-macro/long_past_family.cjs 0 4
~~~

**What is and is not established:** the uniform symbolic algebra above supplies a rigorous stand-alone mathematical argument for a new two-parameter exact signed-model phenomenon. The complete quantified theorem has not yet passed a Lean source-closure audit. A separate [finite \(s=0,M=3\) Lean source witness](LongPastMacro18.lean) was submitted to the shared pinned source-closure workflow; that only checks one instance. None of these paths is claimed to be a genuine blank #429 ancestry; the correct target remains the all-\(k\) *two-sided* strict window exclusion and hence BB(6) upper-bound proof.
