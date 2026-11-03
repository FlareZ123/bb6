# Independent peer audit of Sheep's r=138 infinite family (Agent 40, R006)

**Date:** 2026-11-03. **Scope:** source-shaped exact mathematical audit plus an independent, executable finite-arithmetic checker. This is an intermediate validation of [Agent 14's theorem and source dossier](../agent14-sheep-even-inverse/ORIGINAL-INVERSE-BRIDGE-20261103.md). It does not decide Sheep or BB(6). Original-source local Lean certification is reported by Agent 14; this independent audit does **not** claim to have rebuilt its entire Lean archive.

## Exact statements and a stronger structural corollary

The previous original-source local Lean theorem is

\[
\forall k\in\mathbb N,\quad \neg\,\operatorname{EvenReach}(10,2^{138+4860k}).
\]

The two rational intermediate families in its proof have the following *stronger, seed-independent* property, deducible from the same exhaustive original-source first-even edge splitting and the elementary arithmetic checked below:

**Proposition (no incoming even-section edges).** Under the exact Sheep \`EvenEdge\` semantics, for every \(k\ge0\), every even section state \(x\), and every \(y\),

\[
\begin{split}
15y+2=2^{141+4860k}&\implies \neg\operatorname{EvenEdge}(x,y),\\
81y+68=2^{143+4860k}&\implies \neg\operatorname{EvenEdge}(x,y).
\end{split}
\]

This strengthening removes any hypothesis that \`x\` itself is blank-reachable. Its mathematical derivation is below. It has **not** been added as a separately kernel-compiled Lean theorem; it is a proof-level corollary of the source-shaped branch algebra and the independently reproduced finite modular exclusions. It is expected to be straightforward to formalize using the existing Agent14 modules. As a consequence, an even-start orbit can enter either family only if its *initial state itself* is already in that family. Since the genuine start is 10 and neither target is 10, their exclusion is not dependent on additional blank-origin invariants.

## Independent derivation

For a generic nonhalting even source \(x=2^a v\), \(a\ge1\), \(v\ge5\) odd, let \(z=F(x)\), \(z-1=2^hu\), \(u\) odd, and \(y=1+3^h u\). The original source algebra gives

\[
(2^{a+1}+1)v+2a=3+2^{h+1}u.
\]

For the target \(dy+c=2^{n_0+4860k}\), let \(D=d3^h\), \(T=D(2^{a+1}+1)\), \(B=(2a-3)D+2^{h+1}(d+c)\). Then any generic incoming edge forces

\[
Tv+B=2^{n_0+h+1+4860k}. \tag{1}
\]

For the exceptional \(v=3\) branch, the exact identity instead is

\[
3D2^a+Da+2D+2^h(d+c)=2^{n_0+h+4860k}. \tag{2}
\]

These were independently checked against the literal \(F,E\) arithmetic in **2,794** (source, target-parameter) instances. The fully generic and exceptional cases are separate; no special case was silently treated as generic.

**First, restrict \(h\) universally.** For the first child, \(h\ge4\) would imply \(2^{141+4860k}\equiv17\pmod{1215}\), whereas it is always \(827\); \(2^{324}\equiv1\pmod{1215}\) and \(324\mid4860\). Thus \(0\le h\le3\). For the second child, \(h\ge2\) would imply \(2^{143+4860k}\equiv149\pmod{729}\), whereas it is always \(635\); \(2^{486}\equiv1\pmod{729}\) and \(486\mid4860\). Thus \(h=0\) or \(1\).

**Second, eliminate exceptional sources.** Equation (2) is \(A2^a+Da+C=2^N\), \(A=3D\), \(C=2D+2^h(d+c)\), \(N=n_0+4860k+h\). The six rows below give the smallest convenient threshold \(a_0\). For every \(a\ge a_0\), the expression lies strictly between \(2^{a+t}\) and \(2^{a+t+1}\), where \(t=\lfloor\log_2 A\rfloor\). This follows from \(2^t<A<2^{t+1}\), the checked inequality \(Da_0+C<(2^{t+1}-A)2^{a_0}\), and induction using \(D(a+1)+C<2(Da+C)\) for \(a\ge1\). For \(1\le a<a_0\), the expression is strictly less than \(2^{n_0}\), while the right side has exponent at least \(n_0\).

| Child | \(h\) | \(A\) | \(D\) | \(C\) | \(t\) | \(a_0\) |
|---|---:|---:|---:|---:|---:|---:|
| 1 | 0 | 45 | 15 | 47 | 5 | 3 |
| 1 | 1 | 135 | 45 | 124 | 7 | 1 |
| 1 | 2 | 405 | 135 | 338 | 8 | 3 |
| 1 | 3 | 1215 | 405 | 946 | 10 | 1 |
| 2 | 0 | 243 | 81 | 311 | 7 | 6 |
| 2 | 1 | 729 | 243 | 784 | 9 | 3 |

**Third, exclude large generic valuation \(a\).** The six respective cutoffs \(a_0\) are \(8,10,12,14\) and \(11,13\). At the cutoff, the following independently checked base facts hold: \(B\) is odd, \(1<B<2^{a_0}\), and \(2D<2^{a_0}\). Since \(B(a+1)=B(a)+2D\), induction preserves \(1<B(a)<2^a\) at all \(a\ge a_0\). Now \(M=2^{a+1}+1\) divides \(2^N-B\) by (1). But \(2^{a+1}\equiv-1\bmod M\), so \(2^N\bmod M\) is either \(2^r\) or \(-2^r\) with \(0\le r\le a\). A positive odd \(B\) strictly between \(1\) and \(2^a\) equals neither power; also \(B+2^r<M\), precluding the negative case.

**Finally, close every small generic valuation.** For odd \(v\), (1) forces \(2^N+C'\equiv T\pmod{2T}\), with \(C'=2T-B\) when \(B\ge0\) and \(C'=-B\) when \(B<0\). The independent audit includes the one negative-B branch (first child \(h=3,a=1,B=-133\)). Set \(p=\operatorname{ord}_T(2)\) and \(q=p/\gcd(p,4860)\). Because \(N\ge1\), the residue of \(2^N\) modulo \(2T\) has period \(p\) and the sequence with \(k\) has period \(q\). The standalone checker reconstructs and verifies **all 62** \((h,a)\) branches and **all 221** distinct k-period representatives. None satisfy the required congruence. Maximum \(p\) encountered is 6318. These are independently calculated exact integers, without importing Agent14's generator or lookup tables.

All possible original-source even incoming branches are therefore eliminated. The deduction is stronger than a blank-root-only last-predecessor contradiction, but it remains an intermediate structural corollary of Agent14's technique rather than a claim of independent discovery of its residue family.

## Reproduction, verification grade and remaining work

Run \`python audit_r138_independent.py\` (Python standard library). It independently verifies 2,794 exact even-return algebra instances, all 62/221 finite constraints, both universal high-h congruences, six high-a signed gap induction bases, and six exceptional-power interval bases. One should still independently inspect Agent14's reconstructed Lean proof and validate its original-source imports and \`#print axioms\` after GitHub Actions can execute jobs again. The existing manual workflow uses upstream Cryptids at commit \`ced8f9f44f67a167d5ecc03e687b048c67926371\`; its workflow requests Lean 4.35.0-rc4, while Agent14's local successful audit used Lean 4.36.0-rc2. These are explicitly different verification environments.

**Scientific status:** exact independent mathematical branch analysis with executable finite certificates; a seed-independent edge corollary on paper; no new original-source full Lean build by this reviewer; no outside-prior-art novelty certification; no exact BB(6) value or universal machine bound.
