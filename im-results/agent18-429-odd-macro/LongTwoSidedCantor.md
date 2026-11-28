# Infinite two-sided #429 signed windows with radius asymptotic to log4(rank)

**Status:** Exact **paper-level** arithmetic construction, with direct BigInt sample replay; *not* all-parameter Lean certified. Synthetic exact signed graph, **not** authentic blank-source ancestry and **not** a wide crossing of radius \(\asymp4^k/k\).

## Exact one-parameter theorem

For every integer R≥10, set \(F_R=69,4161,66645\), according as R≡1,2,0 (mod3), and
\[
D=4^{R-1}+F_R,\quad h=2(D-14182)/63,\quad k=228+h,\quad T=4^k.
\]
The three F values have **only 0/1 base-four digits** in exponents below 9, and \(4^{R-1}+F_R\equiv7\equiv14182\pmod{63}\); hence h is a positive **even** integer, k is even and the R base-four digits \(\beta_R(D)\) are all 0 or 1, with the highest digit 1. Let \(q=k-2R-300>0\), \(N=3k-2R-74\).

At the exact doubled-rank **center** \((P,Y)=(2T+4,\ 2\cdot4^h)\) there exist *both*:

1. An exact strict-interior **backward** halfstep path of length N, with reverse-chronological word
\[
\boxed{0^{227}\ 1\ 0^{k-5}\ 111\ 0^{k-R}\ \beta_R(D)\ 0^q}.
\]
2. An exact strict-interior **forward** halfstep path of length h, with chronological word \(0^h\), ending at \((P+3h,2)\).

Every even-rank/A-phase ordinate is even, so pairing chronological halfsteps gives actual exact signed **radix-16 q0 macro** paths. The center macro state is \((T+2,4^h)\), with backward path length N/2 and forward zero word length h/2, ending at \((T+2+3h/2,1)\). Since N>h, this gives a symmetric signed macro window radius **h/2**, or radius **h halfsteps**.

As R tends to infinity, \(h\sim(2/63)4^{R-1}\), \(k=h+228\), and N/k→3. Therefore
\[
\boxed{\limsup_{k\to\infty}\max_{\text{strict center heights }Y}
 \frac{\text{symmetric halfstep window radius at }(2\cdot4^k+4,Y)}{k}\ \ge\ 1}
\]
(and the equivalent macro-radius/k limsup is at least \(1/2\)). In particular, a uniform source-level **no-cross cutoff at any halfstep radius \(ck\) with c<1** is false in this broad synthetic signed graph. This says nothing about larger linear thresholds Ck with C≥1, and nothing about the **exponentially larger** unresolved \(\lfloor4^k/[128(k+1)]\rfloor\) radius.

## Exact cancellation proof

The first 227 reverse zeros cost \(3\cdot227-2=679\) in rank and increase height from \(2\cdot4^h\) to \(T/2\). The following inverse one has cost 9 and offset 12, producing height \(672=42\cdot4^2\). Another \(k-5\) zeros increase height to \(21T/32\). Three reverse ones, with alternating costs 9,3,9, cancel **the entire leading T term**, leaving
\[
H=28364+63h=\boxed{2D}.
\]
The next \(k-R\) zeros increase height to \((2D/4^R)T\). For the R restricted base-four bits \(d_i\), after j bits the exact inverse recurrence unwinds to
\[
 y_j=2T D_{\rm suffix,j}/4^{R-j}+
      \sum_{i\le j}4^{j-i}d_i(\Delta+C_i-c_i),
\]
with \(\Delta<10k\), \(C_i\le9i\), \(c_i\in\{4,12\}\) for ones. Since the remaining suffix has only base-four 0/1 digits, its height is strictly below \(2T/3\) with margin \(2T/4^R\). At j=R the T term **again vanishes exactly**, leaving positive \(E_R<4k4^R\). The last q reverse zeros finish at height
\[
 0<E_R4^q<(4k/4^{R+300})T,
\]
still strictly interior. Every reverse rank is ≥\(2T-9N>2T-27k\), while all checkpoint heights obey the strict cone. For every R≥10, elementary bounds \(k<4^R\), \(R\le k/16\), and \(T>100k4^{2R}\) make the margins positive; within zero runs the last reverse point is the height maximum. Each inverse-one error term \(\Delta+C_i-c_i\) is positive. This is the same exact source-aligned two-level cancellation established in [LongPastUniformM.md](LongPastUniformM.md), specialized to M=3, s=2 and a *free* R.

For the forward portion, the center has height \(2\cdot4^h\). Successive forward zeros divide this by four and increase the doubled rank by 5/1 in alternating phases; h even moves add rank exactly 3h and end at height 2. Heights strictly decrease and ranks increase, so the cone holds throughout. All even/A heights are even. The corresponding h/2 macro zero steps divide macro ordinate by sixteen each time and add +3 to macro rank.

## Concrete checked instances

| R | F_R | h | k | backward N halfsteps | forward h halfsteps | h/k |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 10 | 69 | 7,874 | 8,102 | 24,212 | 7,874 | .97186 |
| 11 | 4,161 | 32,970 | 33,198 | 99,498 | 32,970 | .99313 |
| 12 | 66,645 | 134,818 | 135,046 | 405,040 | 134,818 | .99831 |
| 13 | 69 | 532,162 | 532,390 | 1,597,070 | 532,162 | .99957 |

The reproducible [long_two_sided_cantor.cjs](long_two_sided_cantor.cjs) **symbolic** checker verifies the R-family modular code, both exact cancellation identities, and sufficient strict-cone inequalities without constructing 4^k. Its **direct** mode (k≤200,000) reconstructs the large signed rank, replays all nonzero inverse bits, validates positive strict endpoints for every compressed zero run, independently pairs the chronological halfsteps into exact original radix-16 macro digits and checks their integrality and final center, and checks the forward macro zero endpoint. Run Node.js with no dependencies: `node im-results/agent18-429-odd-macro/long_two_sided_cantor.cjs 10 11 12`.

Exact signed BigInt reverse and forward replay passed for R=10, R=11, and R=12; nonzero inverse digits were executed individually, zero runs were fast-forwarded using exact phase-cost identities, every terminal cone and A-height parity checked. The existing [long_past_cascade.cjs](long_past_cascade.cjs) contains the equivalent two-reset arithmetic for a fixed leading-exponent choice, and [LongPastUniformM.md](LongPastUniformM.md) proves its uniform symbolic bounds.

For a smaller fixed k=430 witness, [LongPastMacro430.lean](LongPastMacro430.lean) contains an exact 740-step past macro path and 101-step future zero macro path centered at \((4^{430}+2,4^{202})\), submitted for pinned Lean source-closure. That fixed witness uses an earlier R=8 parametrization rather than this R≥10 family.

**Limitations:** No authentic q0 blank-root membership, no two-sided window on the exponentially longer scale, and no BB(6) upper bound. A universal no-crossing cutoff with a **larger** linear coefficient remains possible; third resonance or restricted authentic-root information could be decisive.
