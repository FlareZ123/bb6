# A second resonant cancellation: strict #429 signed prehistories of asymptotic length (2190/583)·k

**Status.** This is a new **uniform symbolic construction with a paper proof and independently executed exact signed halfstep/radix-16 macro arithmetic**. Its all-parameter proof is not yet accepted by Lean. It concerns a *synthetic signed macro graph*, not a blank-tape #429 orbit, a two-sided wide crossing, or a BB(6) bound.

## Statement

For every **even** integer \(s\ge2\) define
\[
\begin{aligned}
F_s&=\begin{cases}
66645 &s\equiv0\pmod6,\\
4161 &s\equiv2\pmod6,\\
69 &s\equiv4\pmod6,
\end{cases}\\
R&=s+6,\qquad D=4^{s+5}+F_s,\qquad
B=882\cdot4^s+133-\frac{63s}{2},\\
h&=\frac{2(D-B)}{63},\qquad
m=3+14\cdot4^s,\qquad
k=m+1+h,\qquad T=4^k.
\end{aligned}
\]
These are positive integers; \(m\) is odd, \(h,k\) even, \(k>4R+20\), \(k\le28\cdot4^s\). All base-four digits of \(D\) are **0 or 1**, and \(D\) has exactly \(R\) digits. Write \(\beta_R(D)\in\{0,1\}^R\) for its base-four expansion, **most significant digit first**.

At the exact doubled-rank signed halfstep center
\[
(P,Y)=\left(2\cdot4^k+4,\ 2\cdot4^h\right)
\]
there is a valid strict-interior backward history whose reverse-chronological bit word is
\[
\boxed{0^m\,1\,0^{k-3-s}\,111\,0^{k-R}\,
       \beta_R(D)\,0^{k-2R-20}.}
\]
Its exact length is
\[
\boxed{N=m+3k-3s-31.}
\]
Every even-rank/A-phase state has **even ordinate**, and N is even. Thus the chronological paired-bit word yields an exact signed radix-16 macro path of length \(N/2\), ending at \((4^k+2,4^h)\). Unlike [LongPastMultiReset.md](LongPastMultiReset.md), this new center has \(Y=2\cdot4^h\), not two; its endpoint may have outgoing edges. We assert **a valid lower bound on inverse depth**, not maximality.

Moreover
\[
\lim_{s\to\infty,\;2\mid s}\frac{N}{k}
=3+\frac{441}{583}=\frac{2190}{583}
\approx3.756432247.
\]
In particular, for infinitely many \(k\) and at the **same coefficient and residue** \(a=2,b=4\), the maximum one-sided strict predecessor depth over admissible center heights exceeds \((2190/583-o(1))k\). The previous geometric M=3 fixed-height construction had asymptotic coefficient three; this disproves any proposed **uniform 3k one-sided cutoff**.

## The two exact cancellations

The first tuning is the familiar identity
\[
m=3+14\cdot4^s,\qquad 3m-9=42\cdot4^s.
\]
Put \(r=k-3-s\) (odd). Starting at \(P=2T+4,\ Y=2\cdot4^h\), the first \(m\) reverse zeros reach height \(T/2\), and the first one reaches height \(3m-9=42\cdot4^s\). A further \(r\) zeros reach height
\[
42\cdot4^{s+r}=42\cdot4^{k-3}=\frac{21}{32}T.
\]
The current rank is \(p_0=2T-\delta\), where
\[
\delta=3(m+r)+1=6m+3h-5-3s.
\]
Because \(r\) is odd, three reverse ones have costs 9,3,9 and satisfy the explicit checkpoint identities:
\[
\begin{aligned}
\frac{21}{32}T
 &\longmapsto \frac58 T+\delta-3\\
 &\longmapsto \frac12 T+5\delta-4\\
 &\longmapsto 21\delta-7.
\end{aligned}
\]
The huge \(T\)-contribution cancels **exactly** after the third one. The residual height is
\[
H=21\delta-7
 =1764\cdot4^s+63h+266-63s
 =2B+63h=\boxed{2D}.
\]
Thus the next \(L=k-R\) reverse zeros take the height to
\[
H4^{k-R}=\frac{2D}{4^R}T.
\]

The **second cancellation** is encoded by the base-four \(0/1\) digits of D. Since \(D=\sum_{i=1}^R d_i4^{R-i}\) and every digit \(d_i\) is zero or one, the next \(R\) inverse bits \(d_1,\ldots,d_R\) remove *exactly* the term proportional to \(T\). Write \(p_{\mathrm{in}}=2T-\Delta\) for the rank immediately before that block; \(\Delta=\delta+21+3L\). After \(j\) bits, let \(C_i\) be the accumulated rank decrease through bit i (\(C_i\le9i\)), and \(c_i\in\{4,12\}\) the inverse-one offset. Unwinding the exact halfstep equations gives
\[
\boxed{
 y_j= 2T\,\frac{D_{\mathrm{suffix},j}}{4^{R-j}}
       + E_j,\qquad
 E_j=\sum_{i=1}^{j}4^{j-i}d_i(\Delta+C_i-c_i)
}
\]
where \(D_{\mathrm{suffix},j}=\sum_{i=j+1}^R d_i4^{R-i}\) consists of the unconsumed base-four digits. In particular \(D_{\mathrm{suffix},R}=0\), so
\[
\boxed{y_R=E_R,\quad 0<E_R<4k4^R.}
\]
The second large-\(T\) cancellation is **exact**, not merely a floating-point approximation. The final \(k-2R-20\) zeros then extend the history by almost another \(k\) moves.

## Arithmetic of the parameters

The integers \(4^3=64\equiv1\pmod{63}\) and \(882\equiv0\pmod{63}\), \(133\equiv7\pmod{63}\) give \(B\equiv7\pmod{63}\) when s is even. The three values of \(F_s\) were chosen so that \(D\equiv7\pmod{63}\) for each even residue class of s mod 6:
\[
 4^{s+5}+F_s\equiv
 \begin{cases}16+54,\\4+3,\\1+6\end{cases}
 \equiv7\pmod{63}.
\]
Therefore \(h=2(D-B)/63\) is an **even integer**. Its closed expression
\[
h=\frac{284}{63}4^s+s+\frac{2(F_s-133)}{63}
\]
makes positivity and the asymptotics transparent. \(D\) is manifestly a restricted base-four integer: its leading power is \(4^{s+5}\), with fixed low-bit supports
\[
\begin{array}{c|l}
s\bmod6&\text{exponents of the non-leading 1 bits}\\\hline
0 &8,5,3,2,1,0\\
2 &6,3,0\\
4 &3,1,0
\end{array}
\]
which do not overlap the leading exponent for \(s\ge2\) in the respective classes. Hence \(\beta_R(D)\) really is a word of length \(R=s+6\) in \(\{0,1\}\). The formula for k gives
\[
 m=14\cdot4^s+3,\qquad
 k=\frac{1166}{63}4^s+s+4+\frac{2(F_s-133)}{63},
\]
so \(m/k\to882/1166=441/583\). The displayed word length simplifies to \(m+3k-3s-31\) by elementary cancellation; since m is odd, k and s are even, N is even.

## Uniform strict-cone and exact-lattice proof

All checks are for genuine **integer** halfstep states \(p\ge4,\ y>0,\ 3y<p\), including the original parity guard at even/A ranks.

Useful elementary bounds, valid for all even s≥2, are
\[
14\cdot4^s<k\le28\cdot4^s,\quad
R=s+6\le k/16,\quad
4^R=4096\cdot4^s>100k,\quad
T=4^k>100k4^{2R}.
\]
The k-upper bound follows by checking the three fixed \(F_s\) values at their first admissible s (\(s=6,2,4\), respectively), then using geometric growth; the remaining bounds follow immediately. The total reverse length \(N<4k\) and each rank cost is ≤9, so **every** reverse rank is at least \(2T-36k\).

The first \(m\) zeros, the isolated one, the \(r\) zeros and the three ones are strict: their maximal heights are respectively \(T/2\), \(42\cdot4^s\), \(21T/32\), \(5T/8+\delta-3\), \(T/2+5\delta-4\), and \(2D\). Each is positive and has triple smaller than \(2T-36k\). The tightest large-height case \(21T/32\) has triple \(63T/32=2T-T/32\), and \(T/32>36k\). Within a zero run the height increases fourfold on each inverse step and the rank strictly decreases, so checking its last vertex also checks all earlier vertices.

After the \(L\) zeros, the exact height is \(2DT/4^R\). A restricted base-four integer satisfies \(D\le(4^R-1)/3\), hence this height is below \(2T/3-2T/(3\cdot4^R)\), safely in the strict cone. During the next \(R\) inverse digits, the exact identity above gives \(E_j\ge0\) and
\[
E_j\le(\Delta+9R)\sum_{i=1}^j4^{j-i}d_i
      <4k4^R.
\]
Here \(\Delta=\delta+21+3L<10k\), \(R\le k/16\), and every summand with a 1 is **strictly positive** because \(\Delta>12\). For every proper suffix, \(D_{\mathrm{suffix},j}\le(4^{R-j}-1)/3\), so
\[
 3y_j
 <2T-2T4^{-R}+12k4^R
 <2T-36k\le p_j,
\]
using \(T>100k4^{2R}\); for \(j=R\), the leading term vanishes and the strict inequality is easier. Positivity holds because an unconsumed 1 gives a positive leading term, whereas once all leading digits are consumed \(E_j>0\). Thus **all R digits are exact strict predecessors**. This argument uses no heuristic random-word assumptions or interval rounding.

Finally the suffix of \(q_f=k-2R-20>0\) zeros has
\[
0<y_{\rm final}=E_R4^{q_f}
   <\frac{4k}{4^{R+20}}T
   <\frac{T}{4^{18}},
\]
while rank remains \(\ge2T-36k\); it is therefore strict throughout.

The halfstep rank cost is always odd, so phases alternate. Reverse zero makes the new height a multiple of four. Reverse one with an even *new* rank has even new height because \(z=4y-q-12\) with even q; reverse one with an odd new rank need not impose a parity guard. Consequently **every even-rank ordinate is even**, starting from even center \((P,Y)\). Since N is even the final backward state is again even/even and the chronological halfsteps pair into the *actual* q0 signed macro digits \(0,1,4,5\) with offsets \(0,6,18,32\). No phase-relaxed or rational ghost path is used.

## Reproducibility and concrete instances

[long_past_cascade.cjs](long_past_cascade.cjs) has a compact independent verifier. It fast-forwards only all-zero inverse blocks by their **exact alternating-cost formula** (the last vertex is the strictness maximum), executes every one literally with BigInt, checks all A-phase parity, and constructs the chronological source macro word by pairing *run-length encoded bits*. It then independently replays every nonzero radix-16 digit and fast-forwards the exact divisions by powers of 16 along zero blocks, checking source divisibility and strictness. The macro endpoint is \((4^k+2,4^h)\).

~~~sh
node im-results/agent18-429-odd-macro/long_past_cascade.cjs 2 4 6 8
~~~

| s | m | h | k | strict reverse N | N/k | nonzero macro digits |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 227 | 202 | 430 | 1,480 | 3.44186 | 6 |
| 4 | 3,587 | 1,156 | 4,744 | 17,776 | 3.74705 | 6 |
| 6 | 57,347 | 20,582 | 77,930 | 291,088 | 3.73525 | 8 |
| 8 | 917,507 | 295,568 | 1,213,076 | 4,556,680 | 3.75630 | 7 |

The finite replay does **not** substitute for the uniform argument; the latter is the basis of the asymptotic claim and merits Lean formalization. It does provide a directly reproducible independent check against mistakes in the closed formulas and source macro pairing.

## Relevance and limitations

These are exceptionally long **one-sided** source-aligned histories ending at near-power rank \(a4^k+b\), with fixed \(a=2,b=4\) and a carefully selected center height. The mathematical obstruction demonstrates that a universal inverse-depth cutoff \(\le3k\) is false and even a universal \((c\,k)\) cutoff with \(c<2190/583\) fails for infinitely many k. It **does not** furnish a long future suffix at the same center, establish a two-sided CrossWindow, prove an authentic q0 root trajectory, or decide BB(6). The earlier all-scale wide-window target still has radius \(\asymp4^k/k\), exponentially greater than these \(O(k)\) paths. A stronger attack would seek a bounded/unbounded hierarchy of *additional* exact resonant cancellations and prove whether the depth-to-log-rank ratio remains bounded or grows without bound.
