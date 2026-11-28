# Exact reverse-interval exclusion of the first ten wide-window scales

**Scope and status.** A deterministic, exhaustive **BigInt computation** excludes a full preceding wide-window trace at every rank
\[
P=a4^k+b,\qquad a\in\{1,2\},\quad 0\le b<9,\quad 11\le k\le20.
\]
The largest backward interior depth found in the 180 rank cases is **57** (k=20,a=1,b=6). The required preceding radius \(\lfloor4^k/(128(k+1))\rfloor\) is at least **2,730**, so a full wide crossing is impossible in this finite scale range. This is an exhaustive integer **computational certificate, not a Lean-kernel theorem**. It does not decide an unbounded #429 root family, establish the all-k strip exclusion, or bound BB(6).

The exhaustive engine and tiny-universe independent test are in [wide_reverse_intervals.cjs](wide_reverse_intervals.cjs). It uses the positive strict interior model of [Q0HalfStep](../agent1-429-q0-23-7/Q0HalfStep.lean) with actual phase-dependent rank costs and inverse offsets, not a relaxed modulo-only model. The search ignores additional lattice restrictions (such as even height at A phases), and therefore proves impossibility for an overapproximation of the exact graph if the arithmetic results are accepted.

## Exact mathematical invariant

Every half-step has current rank \(p\), ordinate \(y\), and bit \(d\in\{0,1\}\), with \(4y'=y+d\,p+c(s,d)\); its rank increment is the odd integer \(\ell(s,d)\). Phase \(s\) is parity of \(p\). Hence the predecessor phase is odd iff the current \(p\) is even. The two possible inverse steps are:

| predecessor phase | digit 0 | digit 1 |
| --- | --- | --- |
| odd | \(q=p-1,\ z=4y\) | \(q=p-3,\ z=4y-q-4\) |
| even | \(q=p-5,\ z=4y\) | \(q=p-9,\ z=4y-q-12\) |

The predecessor is interior exactly when \(q\ge4\), \(1\le z\le\lfloor(q-1)/3\rfloor\). Both inverse actions are tested; source-specific constraints can only strengthen the exclusion.

For fixed central rank \(P\), the root node carries all integer central heights \(h\in[1,\lfloor(P-1)/3\rfloor]\) with current \(p=P\) and affine height \(y=A h+B\), initially \(A=1,B=0\). A depth-\(j\) node \((p,A,B,L,H,j)\) represents every central integer \(h\in[L,H]\) yielding the chosen reverse word with strict positive ancestors at all \(j\) positions. Each child replaces \(A\) by \(4A\), replaces \(B\) by \(4B-d(q+c)\), and intersects the old interval with
\[
 \left[
 \left\lceil\frac{1-B'}{A'}\right\rceil,\ 
 \left\lfloor\frac{\lfloor(q-1)/3\rfloor-B'}{A'}\right\rfloor
 \right].
\]
Empty intersections are rejected. This is **exact**, including negative affine offsets, because floor and ceiling divisions use signed BigInt. The invariant follows by induction on depth: every legitimate predecessor selects one of the children, and every retained integer height yields that exact predecessor configuration. No floating point, height cutoff or sampling occurs.

The search records the greatest depth of a nonempty node. As every reverse move decreases \(p\) by at least one, the unbounded traversal is finite; the script uses a cutoff of 64 and explicitly **fails** rather than claiming certification if any node reaches depth 64. Thus reported maxima below 64 establish that no central height supports 64 consecutive strict predecessors. The finite covering argument depends on the exhaustive arithmetic execution, and does **not** assume uniqueness of predecessor.

## Exhaustive output and proof interface

Each row aggregates all 18 ranks at that k. Node counts include the initial interval and all nonempty descendants.

| k | maximum reverse depth | explored nodes | wideRadius(k) |
| ---: | ---: | ---: | ---: |
| 11 | 34 | 95,473 | 2,730 |
| 12 | 42 | 191,228 | 10,082 |
| 13 | 36 | 382,466 | 37,449 |
| 14 | 37 | 765,014 | 139,810 |
| 15 | 47 | 1,530,305 | 524,288 |
| 16 | 50 | 3,060,815 | 1,973,790 |
| 17 | 51 | 6,121,594 | 7,456,540 |
| 18 | 54 | 12,243,166 | 28,256,363 |
| 19 | 54 | 24,486,522 | 107,374,182 |
| 20 | 57 | 48,973,194 | 409,044,504 |

Reproduce with Node.js BigInt support:

~~~sh
node im-results/agent18-429-odd-macro/wide_reverse_intervals.cjs --selftest
node im-results/agent18-429-odd-macro/wide_reverse_intervals.cjs 11 20 64
~~~

Self-test compares the symbolic search to independent height-by-height replay for **all 497 ranks 4 through 500**, plus the k=12,a=1,b=0 rank; that larger rank agrees with the independently run direct 5,592,405-height enumeration (maximum depth 40). The full scan was executed with mathematically identical functions in a JavaScript V8 runtime because this invocation's local shell and Python entry points returned ClientError before executing any commands. The checked-in source has not been run as a repository CI job; do not label this a source-accepted Lean proof.

As [Q0StripCross](../agent1-429-q0-23-7/Q0StripCross.lean) proves equivalence of the exact wide window and its signed carry formulation under its size hypotheses, the finite result points to a **smaller remaining proof obligation**: prove the all-scale exclusion for \(k\ge21\), and separately import this finite arithmetic certificate into a trustworthy formal consumer. The original q0 reduction only requires \(k\ge12\), while the Agent18 odd-reset theorem also allows \(k=11\); both ranges are now computationally covered through 20. The old \(k\ge12\) interface remains the only compiled theorem until that composition is accepted.

## Numerical consequences for authentic-root parameter interfaces (conditional on source acceptance)

The published wide-window reductions choose the crossing exponent **only at** \(k=t_0\) or \(k=t_0+1\), where \(4^{t_0}\le 2p<4^{t_0+1}\) and \(p\) is the signed-macro starting rank. Therefore \(2p<4^{20}\) forces \(k\le20\). This gives sharp, easily audited candidate-parameter ranges from the computational certificate:

| existing signed source reduction | doubled starting rank \(2p\) | largest parameter satisfying \(2p<4^{20}\) |
| --- | --- | ---: |
| Agent 1 q0: \(m=8u+5,\ p=24u+22\) | \(48u+44\) | **\(u=22,906,492,244\)** |
| Odd FF: \(m=13+16t,\ p=53+48t\) | \(106+96t\) | **\(t=11,453,246,121\)** |
| Odd FE: \(m=8+16t,\ p=36+48t\) | \(72+96t\) | **\(t=11,453,246,121\)** |

The arithmetic is \(4^{20}=1,099,511,627,776\), and the maxima are respectively \(\lfloor(4^{20}-45)/48\rfloor\), \(\lfloor(4^{20}-107)/96\rfloor\), and \(\lfloor(4^{20}-73)/96\rfloor\). The existing q0 wide theorem starts at \(u\ge10^6\), and the odd FF/FE theorems start at \(t\ge43,750\); their previously certified small-parameter cases address the lower ranges. **If** the 180-rank integer exclusion is imported as an accepted theorem, composition would exclude the respective signed paths at *every* parameter through the values above. It is not presently an original-source accepted parameter exclusion, since the finite computation itself has no Lean proof consumer. For \(2p\ge4^{20}\), the k=20 branch may still be selected in some cases; these displayed bounds are safe sufficient conditions rather than maximal parameter coverage.

## Remaining unknown

Enumeration cost roughly doubles per additional k: 48,973,194 interval nodes for the 18 ranks at k=20. Extending scale by scale is **not** a solution to the unbounded quantifier. A valuable next advance would turn the reverse intervals' structure into a uniform symbolic bound. Otherwise this is a finite-scale check and should not absorb repeated compute. The [fixed-tail rigidity](TemplateRigidity.md) and exact-carry reductions remain complementary routes to the unbounded case.
