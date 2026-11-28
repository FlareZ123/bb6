# Infinite exact two-sided #429 signed windows with symmetric halfstep radius k−18

**New paper-level theorem, exact symbolic derivation and independent BigInt signed-macro replay. Not yet an all-parameter Lean theorem.** The states are synthetic states of the authentic signed #429 halfstep/radix-16 **graph**, not authenticated ancestors of the blank machine. The theorem is about a *linear* window in the logarithmic rank parameter k, not the exponentially larger \(\asymp4^k/k\) two-sided window in the unresolved #429 proof.

## Exact theorem with one free parameter

For every integer \(R\ge10\), let
\[
 F_R=\begin{cases}
 69,&R\equiv1\pmod3,\\
 4161,&R\equiv2\pmod3,\\
 66645,&R\equiv0\pmod3,
 \end{cases}\quad
 D=4^{R-1}+F_R,\quad
 h=\frac{2(D-1015)}{63},\quad
 k=18+h,\quad T=4^k.
\]
Each F has only base-four 0/1 digits below exponent nine, and \(4^{R-1}+F_R\equiv7\equiv1015\pmod{63}\). Therefore \(h\) is positive and **even**, k even, and the R base-four digits \(\beta_R(D)\) are all 0 or 1, beginning with 1. Put \(q=k-2R-300>0\) and \(N=3k-2R-282\).

At the exact doubled-rank signed halfstep center
\[
 (P,Y)=(2T+4,\;2\cdot4^h)
\]
there are **two** strict, source-phase-aligned positive-cone paths:

- A **backward** halfstep path of length **N**, with reverse chronological word
\[
 \boxed{0^{17}\;1\;0^{k-3}\;111\;0^{k-R}\;\beta_R(D)\;0^q.}
\]
- A **forward** halfstep path of length **h=k−18**, consisting of precisely \(0^h\) and ending at \((P+3h,2)\).

Every even-rank/A-phase ordinate is even, and N and h are even. Thus grouping chronological halfsteps produces exact **original q0 signed radix-16 macro** paths centered at \((T+2,4^h)\), with a backward path of N/2 macro steps and a forward path of **h/2** macro zero steps. The forward endpoint is \((T+2+3h/2,1)\). N>h, so the signed graph has a **symmetric strict macro window radius exactly \(h/2=(k-18)/2\)**, or **halfstep radius \(h=k-18\)**, for every R≥10.

As R→∞, \(h\sim(2/63)4^{R-1}\), \(k=h+18\), and \(N/k\to3\). Consequently
\[
 \boxed{\limsup_{k\to\infty}\max_Y
  \frac{\text{symmetric signed halfstep window radius at }(2\cdot4^k+4,Y)}{k}
  \ge1}
\]
with the analogous macro-radius/k limsup ≥1/2. This **falsifies a universal no-crossing bound at any radius \(ck\) with c<1 (halfstep units)** for synthetic strict graph states. It does **not** rule out a larger constant-linear bound and does not challenge the exponential target \(\lfloor4^k/[128(k+1)]\rfloor\).

## Algebraic proof of the backward path

The first 17 inverse zeros from even rank lose \(3\cdot17-2=49\) rank units and multiply height by \(4^{17}\), reaching height \(2\cdot4^{h+17}=T/2\). The next inverse one from odd phase has cost nine and height
\[
4(T/2)-(2T+4-49-9)-12=42.
\]
The next \(k-3\) inverse zeros reach height \(42\cdot4^{k-3}=21T/32\). Because k is even, this zero-run length is odd, so the next three inverse ones have costs 9,3,9. Their enormous T-term cancels **exactly**, leaving
\[
H=2030+63h=\boxed{2D}.
\]
A further \(k-R\) inverse zeros raise height to \((2D/4^R)T\). The R restricted base-four digits \(d_1,\ldots,d_R\) now provide a **second exact cancellation**. If the rank at the start of that digit block is \(2T-\Delta\), with \(\Delta<10k\), and \(C_i\le9i\) is the accumulated cost through digit i, then after j digits the height is
\[
 y_j=2T\,D_{\mathrm{suffix},j}/4^{R-j}
       +\sum_{i\le j}4^{j-i}d_i(\Delta+C_i-c_i),
\]
where \(c_i=4\) or 12 is the phase-dependent offset for a one (zero contributes no offset), and the suffix consists of unconsumed 0/1 base-four digits. The first digit is 1, so the error term stays **strictly positive**. At j=R, the suffix is zero, and the leading \(T\) coefficient vanishes:
\[
0<E_R:=y_R<4k4^R.
\]
The last q reverse zeros yield positive height \(E_R4^q<(4k/4^{R+300})T\).

All predecessor ranks remain ≥\(2T-9N>2T-27k\). Every height is positive and satisfies \(3y<p\): the pre-reset maxima are \(T/2\), \(21T/32\) and the positive intermediate one residues; the digit-block suffix bound is \(3y_j<2T-2T4^{-R}+12k4^R<2T-27k\); the final zeros are extremely small. The sufficient elementary bounds \(k<4^R\), \(R\le k/16\) and \(T>100k4^{2R}\) hold at R=10 and improve for larger R. Within any homogeneous reverse-zero run, each step multiplies height by 4 and decreases rank, so checking its final state checks *every earlier state*. One predecessors landing at even ranks produce even heights (\(4y-q-12\)), and zero predecessors produce multiples of four. Hence all A-phase lattice guards are exact, not phase-relaxed.

## Forward part and exact source macro semantics

From even doubled rank \(P\), each forward zero divides height by four and increments doubled rank by 5 at even phase or 1 at odd phase. The initial height \(2\cdot4^h\) is divisible by the required powers of four, and after h (even) zero steps the height is 2 and rank increases by 3h. Along the forward trajectory heights strictly decrease and ranks increase, preserving \(0<3y<p\) and A-rank even height. Pairing gives exactly h/2 source q0 macro zeros, each dividing macro height by 16 and increasing macro rank by 3. The source macro forward endpoint is \((T+2+3h/2,1)\).

## Reproduction

| R | F_R | h | k | backward N halfsteps | forward h halfsteps | h/k |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 10 | 69 | 8,292 | 8,310 | 24,628 | 8,292 | 0.99783 |
| 11 | 4,161 | 33,388 | 33,406 | 99,914 | 33,388 | 0.99946 |
| 12 | 66,645 | 135,236 | 135,254 | 405,456 | 135,236 | 0.99987 |
| 13 | 69 | 532,580 | 532,598 | 1,597,486 | 532,580 | 0.99997 |

[long_two_sided_cantor.cjs](long_two_sided_cantor.cjs) implements a **symbolic exact-integer checker** for arbitrary R without materializing \(4^k\); for k≤200,000 it additionally runs a **direct independent source macro** replay: every nonzero halfstep, rank-parity lattice, strict compressed zero-block endpoint, and original radix-16 macro digit division is checked. Execute:

~~~
node im-results/agent18-429-odd-macro/long_two_sided_cantor.cjs 10 11 12
~~~

Direct halfstep and original macro replay were independently tested for R10,R11,R12. A separate smaller instance at k=430, center \((4^{430}+2,4^{202})\), has a **740-step past macro path** and **101-step forward macro zero path** in [LongPastMacro430.lean](LongPastMacro430.lean), submitted for Lean source-closure. That earlier k430 witness uses a distinct R=8, s=2 construction, not this simpler s=0 R≥10 family.

**Limitations.** The all-R statement still needs formal source-closure acceptance. This result gives no valid machine reachability from the blank tape, no exponential wide-window crossing, no #429 holdout resolution and no exact BB(6).
