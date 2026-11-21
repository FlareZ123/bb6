# Root32 high-stop exclusion on r = 10592 (mod 16384)

**Status:** the L and corrected P7E1E alternatives are now separately source-accepted on the full t≡31 (mod 32) slice. The D0E/R chain remains a paper-level exact reduction, and the three-way high-stop composition has not been compiled as one Lean 4.36.0-rc2 theorem. This is not yet an accepted high-stop exclusion, a global Machine C result, or a BB(6) result.

## 1. Parameter cylinder

Set

\[
t=256m+31,\qquad q=\frac{t-3}{4}=64m+7.
\]

The existing high-stop inverse reduction gives

\[
CReach(T(1802+6720t))
\Longrightarrow
CReach(D_{0E}(t))\lor CReach(L(t))\lor CReach(P_{7E1E}(t)).
\]

The exceptional R parent-fan result in RRoot32ExceptionalParentFan.md, Section 6, proves that R(t) is unreachable for q≡7 mod64. The forced source chain D0E → E7 → P → R therefore gives

\[
\neg CReach(D_{0E}(t)).
\]

It remains to exclude L(t).

## 2. The L branch

Since t≡3 mod4, the exact odd/odd sum-16 parent theorem and the P0/P2 split in LRoot32OddParentReduction.md show that L reachability would force P0(t). The complete source grammar gives its unique parent

\[
A_0(t)=
(2518584390t+675395581,\;2263923165t+607104414).
\]

Here t≡15 mod16, so the sum of A0(t) is 8 mod16. The odd/odd low-valuation inverse therefore forces

\[
Q(v)=
(9565015110v+7815011328,\;
 9310353885v+7606942617),
\qquad v=q=64m+7.
\]

Substituting v gives

\[
Q=
(612160967040m+74770117098,\;
 595862648640m+72779419812).
\]

Both coordinates are even, the right coordinate is at least six, and

\[
Q_x+Q_y=1208023615680m+147549536910\equiv6\pmod8.
\]

The exact even-right inverse forces its unique direct parent

\[
Q'=
(1208023615680m+147549536908,\;
 297931324320m+36389709905).
\]

The right coordinate of Q' is odd and at least five, while

\[
Q'_x+Q'_y=1505954940000m+183939246813
\equiv1\pmod4.
\]

The source-certified blank_no_odd_sum_one theorem excludes Q'. Thus Q, A0, P0, and L are all unreachable. The locally compiled module Root32HighStopR10592LCore.lean formalizes this chain and proves L unreachable for every t≡31 (mod 32), not merely t≡31 (mod 256). Its closure contains 40 project modules; all imported source blobs match current main, and the audited declarations have only standard Lean axioms, with no sorryAx.

A source-integrity issue was found and corrected during this preflight: MixedOdd16TwoOrbit.lean used CReach without importing its definition from Agent3COrbitIff. Lean's autoImplicit silently treated CReach as a parameter, and the old theorem's axiom report contained sorryAx. Adding the missing import (commit f3aae4fcf0a8ef84d136a92bd3c17108de47e05e) makes the reachability split genuine; the corrected theorem now reports only propext, Classical.choice, and Quot.sound.

This discharges only the L alternative. The high-stop reduction still has separate D0E and P7E1E alternatives; see the following section for the independently accepted P7E1E exclusion. No conclusion about T follows from this section alone.

## 3. The corrected P7E1E alternative

For this cylinder, t ≡ 31 (mod 256), hence t ≡ 31 (mod 32). More generally, the locally compiled source-connected core in `Root32HighStopA4Core.lean` proves

```
¬ RunReach(P7E1E(t))
```

on the entire t ≡ 31 (mod 32) cylinder. Its proof uses the complete even/even parent fan to force D(t), the exact odd-seven inverse to force A4(t), and the odd/odd low-valuation inverse to force the parent (p,q) with q odd and p+q ≡ 1 (mod 4), excluded by `run_no_odd_sum_one`. The 52-module Lean 4.36.0-rc2 closure compiled locally; all 51 imported source blobs match current main and the audited declarations have no `sorryAx`.

This closes the P7E1E alternative on all t ≡ 31 (mod 32), at the residual level only. L is separately source-accepted on the same full slice. D0E/R remains paper-level, and no full high-stop theorem is accepted.

## 4. Exact root-index translation

The exact root32 identity is

\[
17300+22155(t+j)=5\cdot2^{E-17},
\qquad r=32+64j.
\]

As in Root32HighStopR9568.md, the right side is divisible by 256, giving

\[
t+j\equiv196\pmod{256}.
\]

For t≡31 mod256 this forces j≡165 mod256, hence

\[
\boxed{r=32+64j\equiv10592\pmod{16384}.}
\]

The exact-root saturation argument in B2Q0FourStepPath.md gives a natural parameter for every j≥0. Thus the progression is nonempty and infinite.

## 5. Scope

The L and P7E1E alternatives are now separately source-accepted for all t ≡ 31 (mod 32), covering r ≡ 10592 (mod 16384) and the other listed root-index cylinders in the broad class r ≡ 352 (mod 2048). The D0E/R chain is still only a paper-level exact reduction, and the original high-stop three-way decomposition has not been compiled and composed with the two accepted exclusions in one Lean 4.36.0-rc2 theorem. Therefore no complete high-stop exclusion on r ≡ 10592 (mod 16384) is currently accepted. This does not address other root-index classes, other stop families, or all six-state machines. Keep this dossier in im-results/ until the exact composition and axiom audit succeed.
