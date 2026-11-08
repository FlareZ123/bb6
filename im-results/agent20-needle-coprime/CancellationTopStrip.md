# Uniform high-valuation exclusion for Space Needle cancellation feeders

**Status (8 November 2026): locally Lean 4.36.0-rc2 kernel-proved for all natural parameters, standard axioms only.** The mathematical statement is a universal necessary-parent exclusion for the entire cancellation family. It does not prove that any whole cancellation feeder is blank-unreachable for all r, and does not prove Space Needle nonhalting.

## Result

For any positive integer r, let
\[
 a_r=(9^r+5)/2,\quad A_r=2^{a_r},\quad
 K_r+1=2r\,a_r=r(9^r+5),
\]
and let the odd part of the cancellation terminal feeder be \(2q_r+3=P_r(A_r)\), where
\[
 P_0(A)=0,\qquad
 P_{r+1}(A)=A^2P_r(A)+9^r(A-3).
\]
The identity
\[
 (A+3)P_r(A)+9^r=A^{2r}
\]
establishes the exact positive integer cancellation solution corresponding to the terminal exponent K_r.

An incoming predecessor valuation u in the original source-checked Space Needle high-level map must satisfy
\[
 2^{u+1}+3\ \mid\ A_r(2q_r+3)+3-2u.
\]

**Theorem (uniform top strip).** For *every* r>=1 and every u satisfying
\[
 (2r-1)a_r+3\le u+1\le 2r a_r,
\]
the necessary divisibility **fails**:
\[
 2^{u+1}+3\nmid A_r(2q_r+3)+3-2u.
\]
Thus, uniformly for all r, the **highest a_r-2 = (9^r+1)/2 distinct possible predecessor valuations** are ruled out. This is one infinite family of all-time predecessor exclusions per cancellation feeder. It does not cover the lower-valuation remainder.

The same theorem is formulated in three increasingly source-friendly versions in [CancellationTopStrip.lean](CancellationTopStrip.lean):

- CancellationStrip.cancellation_top_no_parent: polynomial form, no free q.
- CancellationStrip.cancellation_top_no_parent_odd: odd-part q form with exact polynomial identity.
- CancellationStrip.cancellation_top_no_parent_source_equation: source-equation form with only \((A_r+3)(2q+3)+9^r=A_r^{2r}\) as feeder premise.

The standalone Lean module defines and proves all dependencies, requires only Lean and its standard Omega tactic, and includes axiom audits. It compiled locally under Lean 4.36.0-rc2 with final theorem axioms **[propext, Classical.choice, Quot.sound]**, no sorry. No existing unverified research module is imported.

## Proof idea

The cancellation identity yields the sparse giant-int numerator
\[
 N_u=A_rP_r(A_r)+3-2u = A_r^{2r}-E_u,\quad
 E_u=3P_r(A_r)+9^r+2u-3.
\]
For the stated u range let
\[
 B=2^{u+1},\quad h=2^{2r a_r-(u+1)},\quad T=A_r^{2r-1}.
\]
Then \(Bh=A_r^{2r}\), \(8T\le B\), \(8h\le A_r\), \(P_r(A_r)<T\), and \(9^r+2u\le A_r\). These inequalities are proved for arbitrary r using the bounds \(8r+1\le9^r\) and \(a_r^2\le2^{a_r}\).

Consequently the exact deficit satisfies
\[
 0<E_u\le Bh,\qquad 0<E_u+3h<B+3.
\]
If \(B+3\) divided \(Bh-E_u\), it would divide
\[
 (B+3)h-(Bh-E_u)=E_u+3h,
\]
a strictly positive integer smaller than the divisor. Contradiction.

The proof is entirely symbolic. The observed r=6 exhaustive arithmetic [audit](R6Cancellation.md) excludes the remaining values for that particular feeder; the universal strip independently proves a large fraction of the r=6 high checks without any enumerative certificate.

## Complementary all-parameter modulus-five obstruction

A second independent source-equation theorem excludes **four entire classes of incoming parent valuations modulo 20** for every positive cancellation parameter, throughout the conservative physical interval `u+1<=2*r*a_r`:

[
 umod20in{0,8,12,16}.
]

Equivalently, `u%4=0` and `u%5 != 4`. The proof is in [CancellationMod5.lean](CancellationMod5.lean), with the exact arbitrary-q source-equation interface in [CancellationMod5SourceEq.lean](CancellationMod5SourceEq.lean). Both modules were locally compiled by Lean 4.36.0-rc2; the final source-equation theorem uses only standard axioms and no sorry.

The proof is elementary but unbounded in r. Since `9^r=1 mod 8`, the cancellation exponent `a_r=(9^r+5)/2` is 3 modulo 4. Consequently `A_r=2^a_r=3 mod 5`. The recurrence `P_{r+1}=A_r^2 P_r+9^r(A_r-3)` gives `P_r(A_r)=0 mod 5`. For `u=0 mod 4`, the prospective denominator `D_u=2^(u+1)+3` is divisible by 5, whereas the numerator `N_u=A_rP_r(A_r)+3-2u` can be divisible by 5 only when `u=4 mod 5`. Four of the five multiples-of-four classes are therefore impossible universally.

The modulo-five obstruction excludes one-fifth of the residue density independently of r. It overlaps the high strip; no naive addition of the two excluded counts is valid. The lower/middle residual inverse valuations, including `u=4 mod20`, remain unbounded.

### Fully constructive terminal feeders

[CancellationTopConstructive.lean](CancellationTopConstructive.lean) proves that for every r>=1 the polynomial `P_r(A_r)` is odd and at least three, so `q_r=(P_r(A_r)-3)/2` is a natural number satisfying the exact cancellation identity. [CancellationTerminalConstructive.lean](CancellationTerminalConstructive.lean) proves the corresponding **original inverse terminal equation in primitive exponent notation**:
[
2^{K_r}=(2^{v_r+1}+3)q_r+3cdot2^{v_r}+v_r+3,
quad v_r=(9^r+3)/2,quad K_r+1=r(9^r+5).
]
Both are locally kernel checked with standard axioms. This removes any appeal to an external existential construction for the synthetic feeder arithmetic, while still requiring the established original-physical bridge to interpret the accelerated edges.

## Exact reachability scope

The original source inverse equation, already formalized in [NeedleGeneralInverse.lean](NeedleGeneralInverse.lean) and [NeedleRootDecisionSource.lean](NeedleRootDecisionSource.lean), makes this divisor condition **necessary** for an actual immediate accelerated parent. The new Lean file proves the arithmetic nondivisibility and a direct source-equation interface. An original-source import into the pinned Cryptids machine and a separate external priority review remain future work.

For r=6 the interval contains 265,721 excluded valuation indices out of 3,188,676 total candidates. No claim that the source counter is globally unreachable follows from this strip alone. For r>=7 the low/middle inverse domain is still completely open. Connecting a uniform lower-valuation restriction to the genuine blank-root halting existential is the decisive missing step.

Keep this in im-results pending proof-level comparison to previous external work and stronger global relevance. It is independent of the exact finite r=6 no-parent computation.
