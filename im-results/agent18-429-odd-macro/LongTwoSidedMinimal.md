# An infinite exact two-sided #429 signed family with symmetric radius k−4

**Status and significance.** A new explicit all-R **paper theorem** in the exact source-aligned signed #429 halfstep/radix-16 q0 macro graph. It sharpens [LongTwoSidedCantor.md](LongTwoSidedCantor.md) (which reached radius k−18) by using **one** inverse-one bit in the first reset, rather than three. The construction gives an infinite family with two-sided halfstep radius **exactly k−4** at near-power ranks with coefficient a=2 and residue b=2. A fixed k=684 instance is present in [LongTwoSidedMacro684.lean](LongTwoSidedMacro684.lean) for pinned kernel source-closure checking. The all-R theorem is not yet Lean-certified. Crucially, these are **synthetic signed graph trajectories**, not reachable blank-machine configurations, not crossings of the exponentially larger radius \(\asymp4^k/k\), and not a BB(6) bound.

## Fully explicit theorem

For every integer \(R\ge6\), put
\[
 D=4^{R-1}+5=4^{R-1}+4+1,\qquad
 h=\frac{2(D-9)}3,\qquad
 k=h+4,\qquad T=4^k,
\]
\[
 q=k-2R-100,\qquad N=3k-2R-96.
\]
As \(4^{R-1}\equiv1\pmod3\), \(D\equiv0\pmod3\), so h is a **positive even integer**, k is even and q>0. The R-digit base-four expansion of D is **exactly**
\[
 \beta_R(D)=1\,0^{R-3}\,11,
\]
containing only zero and one digits.

At doubled-rank signed halfstep center
\[
 \boxed{(P,Y)=(2T+2,\ 2\cdot4^h)}
\]
there are **both** of the following strictly positive cone (\(0<3y<p\)) phase-aligned signed halfstep trajectories:

- A **backward** path of length \(N\), with reverse chronological bit word
\[
 \boxed{0^3\ 1\ 0^{k-1}\ 1\ 0^{k-R}\ 
          1\,0^{R-3}11\ 0^q.}
\]
- A **forward** path of length \(h=k-4\), consisting of exactly \(0^h\) from the center to \((P+3h,2)\).

All even-rank/A-phase heights are even, so their chronological pairings are original **q0 signed radix-16 macro** paths. The center macro state is \((T+1,4^h)\), with a past macro path of length N/2 and a future **zero-macro path of length h/2**, ending at \((T+1+3h/2,1)\). As N>h, a **symmetric strict macro window of radius \(h/2=(k-4)/2\)** exists for every R≥6. The corresponding symmetric halfstep window has **radius k−4**.

Since \(h=(2/3)4^{R-1}-8/3\), k=h+4 and N/k→3,
\[
 \boxed{\lim_{R\to\infty}\frac{h}{k}=1}
\]
and the normalized maximal two-sided window radius in this broad signed graph is at least \(1-o(1)\) in halfstep units, or \(1/2-o(1)\) in macro units, along the coefficient-two near-power ranks \(P=2\cdot4^k+2\). This disproves every proposed uniform signed-graph no-crossing bound at halfstep radius \(ck\) for c<1. It does **not** preclude a larger linear cutoff \(Ck\) with C≥1, and is vastly weaker than the all-k exponential-radius noCross hypothesis required for BB(6).

## Exact cancellation algebra

The center rank is even. Three inverse zeros have rank costs 1,5,1, hence total seven, and multiply the height by 64. Since \(k=h+4\), the height after these three inverses is
\[
 2\cdot4^{h+3}=T/2.
\]
The first inverse one comes from the odd predecessor phase with cost nine and offset 12, so its new height is
\[
4(T/2)-(2T+2-7-9)-12=\boxed2.
\]
The next \(k-1\) inverse zeros (an odd length) take this height to \(2\cdot4^{k-1}=T/2\). Their rank loss is \(3(k-1)-2=3k-5\). Another inverse one from odd phase now lands at even rank
\[
2T+2-7-9-(3k-5)-9=2T-3k-18,
\]
and the new height is
\[
 4(T/2)-(2T-3k-18)-12=3k+6
 =3(h+4)+6=3h+18=\boxed{2D}.
\]
This is the **first exact cancellation** of the enormous \(T\)-coefficient, achieved with a *single* inverse one at each reset.

Next perform \(k-R\) inverse zeros. The height is now
\[
 y_0=2D4^{k-R}=\frac{2D}{4^R}\,T.
\]
Take the R **restricted base-four** inverse bits \(d_1\cdots d_R=10^{R-3}11\). If the rank immediately before this bit block is \(2T-\Delta\), then \(\Delta=3k+18+[3(k-R)-2((k-R)\bmod2)]<7k\). If \(C_i\le9i\) is the accumulated rank loss to stage i, the exact inverse recurrence unwinds into
\[
 y_j=2T\,D_{\rm suffix,j}/4^{R-j}
     + E_j,\qquad
 E_j=\sum_{i=1}^j4^{j-i}d_i(\Delta+C_i-c_i).
\]
Here \(c_i\in\{4,12\}\) is the inverse-one offset at the respective phase. Every summand with \(d_i=1\) is **strictly positive** because \(\Delta>12\). The base-four suffix disappears after all R bits, producing the **second exact cancellation**
\[
 \boxed{0<E_R=y_R<4k4^R}.
\]
Finally the q=k−2R−100 reverse zeros end at a small positive height
\[
 y_{\rm left}=E_R4^q
    <\frac{4k}{4^{R+100}}T.
\]
The reverse path length is exactly
\[
3+1+(k-1)+1+(k-R)+R+(k-2R-100)
  =\boxed{3k-2R-96=N}.
\]

## Global cone and source-alignment checks

Every reverse rank loses an odd positive cost at most nine; because \(N<3k\), its rank stays above \(2T+2-9N>2T-27k\). The three large-height checkpoints before and between the cancellation blocks are \(T/2\), \(T/2\), and \(y_0=(1/2+10/4^R)T\). For \(R\ge6\) all have triple <\(2T-27k\), as \(T=4^k\) is enormous compared with k. In the restricted R-digit block, \(D_{\rm suffix,j}\le(4^{R-j}-1)/3\), yielding
\[
 3y_j < 2T-2T4^{-R}+12k4^R
     < 2T-27k
\]
by elementary bounds \(k<4^R\), \(R\le k/16\), \(T>100k4^{2R}\) (each already true at R=6 and strengthens as R grows). The last q zero steps stay far beneath the cone boundary. Within any reverse-zero block, height increases by four and rank decreases, so the last vertex has the tightest cone inequality. Every one-step residual is positive by the explicit first two reset identities and the positivity of all terms in E_j. Thus **every intermediate vertex** is positive and strictly interior.

Both inverse actions change rank parity. A zero inverse gives height divisible by four, and a one inverse landing at even rank has height \(4y-q-12\), automatically even. Hence the even-rank/A-height lattice guard holds throughout. The initial center has even doubled rank and even height, and N is even; exact chronological halfstep pairing yields the original source q0 signed radix-16 macro operations (digits 0,1,4,5, costs 3,5,4,6, offsets 0,6,18,32), with no phase relaxation.

The **forward** path is simpler: the starting height \(2\cdot4^h\) is divisible by four exactly h times; each forward zero divides it by four, increments rank by cost five or one in alternating phases, and preserves the cone as rank increases while height decreases. Since h is even, h forward zeros increase doubled rank by 3h and end at height two; in the macro graph h/2 forward digit-zero steps increase macro rank by 3 each and end at height one.

## Concrete witnesses and formalization

| R | k | h = k−4 | strict backward halfsteps N | symmetric macro radius h/2 |
| ---: | ---: | ---: | ---: | ---: |
| 6 | 684 | 680 | 1,944 | 340 |
| 7 | 2,732 | 2,728 | 8,086 | 1,364 |
| 8 | 10,924 | 10,920 | 32,660 | 5,460 |
| 9 | 43,692 | 43,688 | 130,962 | 21,844 |
| 10 | 174,764 | 174,760 | 524,176 | 87,380 |

Exact BigInt signed inverse and forward replay was performed for R=6,7,8,9, checking every nonzero halfstep, strictness at the end of each compressed zero run and every even/A parity guard. Direct replay of the chronological original macro word for R=6 was independently checked.

The R=6 witness is especially compact:
\[
\begin{aligned}
k&=684,\quad h=680,\quad N/2=972,\\
\text{macro left state}
 &=\bigl(4^{684}-2923,\;2111029\cdot4^{572}\bigr),\\
\text{chronological macro past word}
 &=0^{286}\;5\;0\;4\;0^{339}\;1\;0^{341}\;1\;0,\\
\text{macro center}&=(4^{684}+1,4^{680}),\\
\text{future word}&=0^{340},\\
\text{macro right state}&=(4^{684}+1021,1).
\end{aligned}
\]
[LongTwoSidedMacro684.lean](LongTwoSidedMacro684.lean) is an original-source Lean file with exact Path and endpoint theorems for both sides, no imported untrusted trace data; its pinned source-closure CI must be checked before calling this particular finite witness formally accepted. The all-R mathematical proof here remains a paper theorem, not yet a quantified Lean theorem.

**Open problem unchanged:** the q0 strict signed *two-sided wide window* excluded by the outstanding #429 proof has radius of order \(4^k/k\), vastly larger than these O(k) constructed windows. The actual blank-machine source orbit is not shown to enter any state above. Neither a BB(6) upper bound nor the exact BB(6) value follows.
