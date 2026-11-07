# Independent high stopping-target exclusions

**Date:** 7 November 2026  
**Status:** the even-right family is source-verified; its integration with Agent20's C70+C23 residual is pending original-source CI.

The high stopping map is
\[
(j,m)\longmapsto
\left(2j+3,\;k(j,m)\right),\qquad
k(j,m)=2^{2m+2}(j+3)-(j+3m+5).
\]

## 1. New even-right unique-inverse cylinder

For
\[
m\geq3,\qquad m\equiv3\pmod4,\qquad
j\equiv m+3\pmod8,
\]
the high target has \(k\) even and
\[
(2j+3+k)\bmod8=3.
\]
The exact even-right inverse has a unique parent:
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
- HighEvenRightResidual.lean: proof that the entire cylinder survives Agent24Phase.highAllowed and an exact halting-iff refinement.
- Original-source CI: [42348489335](https://github.com/FlareZ123/bb6/actions/runs/42348489335) for the source theorem, and [42349021125](https://github.com/FlareZ123/bb6/actions/runs/42349021125) for the prior-sieve theorem and exact residual equivalence. The axiom audit showed no sorryAx.

The explicit subfamily \(j=8q+6,m=3\) is contained in this cylinder. The theorem covers every compatible \(m,j\).

## 2. Independent cross-check of Agent20's C23 cylinder (not a new exclusion)

The congruence
\[
m\geq5,\qquad m\equiv1\pmod4,\qquad
j+8\equiv3m+1\pmod{32}
\]
is equivalent to Agent20's already-established C23 high family
\[
m\geq2,\qquad j\equiv0\pmod4,\qquad
j+7\equiv3m\pmod{32}.
\]
Reducing the first congruence modulo four gives \(j\equiv0\pmod4\); shifting both sides by one gives the C23 congruence. Conversely, the C23 congruence with \(j\equiv0\pmod4\) forces \(m\equiv1\pmod4\), and \(m\geq2\) then implies \(m\geq5\). The eight residue pairs modulo 32 are
\[
(28,1),(8,5),(20,9),(0,13),(12,17),(24,21),(4,25),(16,29),
\]
with the literal \(m=1\) instance excluded by \(m\geq5\).

Agent20 already proves the source exclusion, prior-sieve admission, and exact residual integration in C23Rectangle.lean, C23High.lean, C23Strict.lean, and C23Integration.lean. This is therefore not a new frontier reduction. Its value is an independent reconstruction through the full one-step preimage classification BB6.Agent46.sectionPreimageAll, rather than Agent20's specialized seven_inverse theorem.

For every possible one-step predecessor \((a,b)\), the complete grammar and target residues force
\[
b\geq5,\qquad b\equiv1\pmod2,\qquad
a+b\equiv2\pmod4.
\]
The exhaustive cases are:

1. The \(a=0\) high branch requires \(x+y\equiv0\pmod8\), contradicting \(x+y\equiv7\pmod8\).
2. The \(a=1\) high branch requires \(S\equiv0\pmod{16}\), contradicting \(S\equiv8\pmod{16}\).
3. The direct branch has parent \((x+y-2,(y-2)/2)\), with odd second coordinate and sum \(2\bmod4\).
4. The even-\(a\) bounce branch requires \(x+y\) divisible by \(4\), impossible because \(x+y\) is odd.
5. In the odd-\(a\) high bounce branch, \(v_2(S)=3\) and the cost equation force bounce depth \(n=1\). The parent then has \(a\equiv3\pmod8\), \(b\equiv3\pmod4\), hence \(a+b\equiv2\pmod4\).

Every possible parent violates the blank-orbit odd-right image invariant. This independently validates the same source exclusion without a finite bounce-depth cutoff.

- HighEvenRightSum7Arithmetic.lean: general target residues for the C23 congruence cylinder.
- HighEvenRightSum7Source.lean: complete preimage classification and blank-origin exclusion.
- HighEvenRightSum7Residual.lean: independent proof of prior-sieve admission and exact residual integration, duplicating the role of C23Strict/C23Integration.

Agent24 run 42351346417 compiles both Agent20's original C23 modules and this independent reconstruction. Treat §2 as a cross-check, not an additional excluded cylinder.

## 3. Strongest combined residual and scope

HighEvenRightC23Residual.lean appends the genuinely new even-right obstruction from §1 to Agent20's strongest C70+C23 residual. It preserves the low C70 exclusion, both C70 high rectangles, and the C23 high family. The theorem also proves the new even-right cylinder survives the entire C70+C23 prior predicate.

The combined original-source CI check is pending in [run 42351346417](https://github.com/FlareZ123/bb6/actions/runs/42351346417).

No result here determines whether Machine C halts, bounds the remaining existential parameters, or determines \(BB(6)\).
