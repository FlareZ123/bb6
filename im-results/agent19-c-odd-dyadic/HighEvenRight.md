# Independent high stopping-target exclusions

**Date:** 7 November 2026  
**Status:** first family source-verified; second family submitted for full source CI.

The high stopping map considered here is

\[
(j,m)\longmapsto
\left(2j+3,\;k(j,m)\right),\qquad
k(j,m)=2^{2m+2}(j+3)-(j+3m+5).
\]

These are exact source-section targets in the Agent24/ValSix high reduction. The results below exclude infinite parameter cylinders that survive the preceding Agent24 high predicate.

## 1. Even-right unique-inverse cylinder

For
\[
m\geq3,\qquad m\equiv3\pmod4,\qquad
j\equiv m+3\pmod8,
\]
the high target has \(k\) even and
\[
(2j+3+k)\bmod8=3.
\]
The exact even-right inverse therefore has a unique parent:
\[
(x',y')=(2j+3+k-2,\;(k-2)/2).
\]
The source arithmetic gives \(y'\) odd, \(y'\geq5\), and
\[
(x'+y')\bmod4=2.
\]
The established blank-orbit odd-right image theorem permits only residues \(0\) and \(3\) modulo \(4\). Thus the parent is not blank-reachable, and neither is the target.

- HighEvenRightArithmetic.lean: reusable exact parent arithmetic and high-score bounds.
- HighEvenRightSource.lean: original-source inverse and orbit proof.
- HighEvenRightResidual.lean: proof that the entire cylinder survives Agent24Phase.highAllowed, followed by an exact halting-iff refinement.
- Original-source CI: [42348489335](https://github.com/FlareZ123/bb6/actions/runs/42348489335) for the source theorem, and [42349021125](https://github.com/FlareZ123/bb6/actions/runs/42349021125) for the prior-sieve theorem and exact residual equivalence. The axiom audit showed no sorryAx.

The explicit subfamily \(j=8q+6,m=3\) is contained in this cylinder, but the theorem is stronger and covers every compatible \(m,j\).

## 2. Exceptional sum-seven inverse cylinder

A second, disjoint family is
\[
j=32q+8,\qquad m=32r+5.
\]
Writing \(x=2j+3\), \(y=k(j,m)\), and \(S=x+y+1\), the exact arithmetic gives
\[
y\geq12,\quad y\bmod8=4,\quad
(x+y)\bmod8=7,\quad S\bmod32=24,\quad x\bmod4=3.
\]

The sum-seven case does not have the unique even-right inverse used in §1. Instead, the proof uses the complete one-step preimage classification BB6.Agent46.sectionPreimageAll from SectionAllInverse.lean.

For every possible one-step predecessor \((a,b)\), the classification and these residues force
\[
b\geq5,\qquad b\equiv1\pmod2,\qquad
(a+b)\equiv2\pmod4.
\]
The cases are exhaustive:

1. The \(a=0\) high branch requires \(x+y\equiv0\pmod8\), contradicting \(x+y\equiv7\pmod8\).
2. The \(a=1\) high branch requires \(S\equiv0\pmod{16}\), contradicting \(S\equiv8\pmod{16}\).
3. The direct branch has parent \((x+y-2,(y-2)/2)\), which has odd second coordinate and sum \(2\bmod4\).
4. The even-\(a\) bounce branch requires \(x+y\) divisible by \(4\), impossible because \(x+y\) is odd.
5. In the odd-\(a\) high bounce branch, the 2-adic valuation \(v_2(S)=3\) and the cost equation force bounce depth \(n=1\). The parent then has \(a\equiv3\pmod8\), \(b\equiv3\pmod4\), hence \(a+b\equiv2\pmod4\).

Every possible parent therefore violates the blank-orbit odd-right image invariant. This proves source non-reachability without a finite bounce-depth cutoff.

- HighEvenRightSum7Arithmetic.lean: target residues and parent arithmetic.
- HighEvenRightSum7Source.lean: complete preimage classification and blank-origin exclusion.
- HighEvenRightSum7Residual.lean: proposed prior-sieve admission and combined exact halting criterion.

**CI status:** pending full Agent24 original-source run. Do not cite this second family as formally verified until the run containing HighEvenRightSum7Source.lean and HighEvenRightSum7Residual.lean completes successfully.

## 3. Scope and remaining problem

These results remove two new infinite high-parameter cylinders from the exact Machine C halting predicate. They do not bound the remaining existential parameters and do not determine whether Machine C halts. Consequently, they do not yet determine \(BB(6)\).

Next:
- complete the pending source and prior-sieve CI audit;
- have an independent researcher check the complete sum-seven predecessor case split and the Agent24Phase.highAllowed admission proof;
- test the companion residue cylinder \(j\equiv24,\ m\equiv21\pmod{32}\), which has the same sum-seven target residues but is not covered by the current second-family theorem;
- integrate only source-verified families into the strongest residual criterion.
