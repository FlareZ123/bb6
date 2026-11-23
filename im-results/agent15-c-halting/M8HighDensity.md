# Exact arithmetic density of one M8-forbidden high-stopping cylinder

**23 November 2026.** This is a mathematically proved modular classification of the *particular quotient-parity M8 cylinder* in the second Machine C stopping family. Its source-level nonreachability theorem [M8GenericHigh.lean](M8GenericHigh.lean) compiled under signature-compatible Lean source stubs without `sorryAx`; the full original-source workflow is tracked separately at [run 45099456878](https://github.com/FlareZ123/bb6/actions/runs/45099456878). These density figures do **not** describe the fraction excluded by all filters or decide global machine nonhalting.

## A unique residue for each compatible depth

For every positive **odd** stopping index \(m\), set
\[
B=2^{2m+2},\qquad Q=(B-1)/3=1+4+\cdots+4^m.
\]
In the exact second-family stopping equation
\[
k+j+3m+5=B(j+3),
\]
the right coordinate satisfies
\[
k+2=3W,\qquad W=Q(j+3)-m.
\]
For \(m\ge1\) and \(j\ge0\), \(W>0\). Indeed \(Q\ge4m+1\), so \(Q(j+3)>m\).

Fix any **depth** \(d\ge1\) with
\[
2d\equiv m+1\pmod4.
\]
The quotient-parity M8 obstruction is equivalent to
\[
W\equiv2^{d+1}\pmod{2^{d+3}}.
\]
Because \(Q\equiv1\pmod4\), it is odd and invertible modulo \(M=2^{d+3}\). Consequently there is **exactly one** index residue class
\[
\boxed{j\equiv Q^{-1}(m+2^{d+1})-3\pmod M}.
\]
Every nonnegative \(j\) in this class has \(W=2^d(2+8t)\) for a unique \(t\ge0\). In particular,
\[
k=3\cdot2^d(2+8t)-2.
\]
Since \(d\ge1\), the same congruence automatically implies \(j\equiv m+1\pmod4\), hence \(j\) is even and \((j+m)\equiv3\pmod4\). Therefore all hypotheses of the original Machine C second-stopping sector and M8 quotient-parity exclusion hold. The source-bound Lean theorem `high_m8_diophantine_exclusion` makes this final step explicit, proving \(\neg\operatorname{CReach}(2j+3,k)\) under the established M8 source theorem.

The congruence classes for different allowed \(d\) are pairwise disjoint. Indeed \(W\equiv2^{d+1}\pmod{2^{d+3}}\) implies exactly \(\nu_2(W)=d+1\), which uniquely determines \(d\).

## Exact asymptotic density

For a fixed odd \(m\), each individual depth class is an arithmetic progression of natural density \(1/2^{d+3}\). The compatible depths are:

- \(m\equiv1\pmod4\): odd depths \(d=1,3,5,\ldots\).
- \(m\equiv3\pmod4\): even depths \(d=2,4,6,\ldots\).

The resulting pairwise-disjoint union has exact natural density
\[
\boxed{
\delta_m=
\begin{cases}
\displaystyle\sum_{a\ge0}2^{-(2a+4)}=\frac1{12},&m\equiv1\pmod4,\\[4pt]
\displaystyle\sum_{a\ge0}2^{-(2a+5)}=\frac1{24},&m\equiv3\pmod4.
\end{cases}}
\]
To justify passing from finite unions to the infinite union, the tail with \(d\ge D\) is contained in \(\{j:2^{D+1}\mid W(j)\}\). Since \(Q\) is odd, that set itself occupies one residue class modulo \(2^{D+1}\), of density \(2^{-(D+1)}\). This tends to zero as \(D\to\infty\). Thus the density sum is rigorous.

These are the densities **among all nonnegative second-family high indices \(j\) at one fixed \(m\)** for this exact M8 quotient-parity cylinder. They do not count halting machines or all BB(6) candidates. Their complement remains infinite. A positive-density source exclusion is insufficient to establish Machine C nonhalting.

## Examples and constructive computation

The unique forbidden class is easily generated via the modular inverse of odd \(Q\). Examples:

| \(m\) | \(d\) | modulus \(2^{d+3}\) | forbidden \(j\) residue |
| --- | ---: | ---: | ---: |
| 1 | 1 | 16 | 14 |
| 1 | 3 | 64 | 26 |
| 1 | 5 | 256 | 10 |
| 3 | 2 | 32 | 28 |
| 3 | 4 | 128 | 20 |
| 3 | 6 | 512 | 372 |
| 5 | 1 | 16 | 2 |
| 5 | 3 | 64 | 62 |
| 7 | 2 | 32 | 16 |

The [unbounded-depth tower](M8OddTower.md) is a constructive doubly infinite *subfamily* using explicit geometric sums; the modular inverse formula characterizes the **entire depth-wise M8 congruence class**, including many other heights. The tower separation theorem against an earlier dyadic filter should not be extrapolated to all the classes here.

## A positive-density family surviving the entire former Agent19 high sieve

A stronger theorem [M8GenericLegacyPass.lean](M8GenericLegacyPass.lean) proves that **every** forbidden M8 class at a compatible depth \(d\ge 2m+2\) satisfies the *entire* earlier maintained \`Agent19Joint.highAllowed j m\` predicate. The source-body Lean 4.36.0-rc2 proof uses exact copied definitions of the Agent3 and Agent19 predicates, compiles without \`sorryAx\`, and is still awaiting full original-module import compilation.

Indeed \(W=Q(j+3)-m=2^d(2+8t)\). Using \(B=3Q+1\),
\[
B(j+3)=j+3m+3+3W.
\]
Because \(B=2^{2m+2}\) divides \(W\) for all \(d\ge2m+2\), one has
\[
\boxed{B\mid(j+3m+3).}
\]
This forces zero residues for all earlier Agent19 dyadic-depth congruence tests. The other Agent3/Agent19 high exclusions are defeated by the necessary \(j\equiv m+1\pmod4\), since \(m\) is odd and \(j\) even with \(j+m\equiv3\pmod4\). Lean proves this composition in \`generic_deep_passes_all_legacy_high_sieves\` and couples it with source M8 nonreachability in \`generic_deep_new_exclusion\`.

In particular, the **entire union** over compatible deep depths consists of candidate indices that were allowed by the earlier sieve and are now excluded. Its exact natural density among all \(j\ge0\) at fixed odd \(m\) is
\[
\delta_m^{\mathrm{new}}=
\begin{cases}
\displaystyle\sum_{a\ge0}2^{-(2m+6+2a)}=\frac{1}{3\cdot2^{2m+4}},
  & m\equiv1\pmod4,\\[6pt]
\displaystyle\sum_{a\ge0}2^{-(2m+5+2a)}=\frac{1}{3\cdot2^{2m+3}},
  & m\equiv3\pmod4.
\end{cases}
\]
For \(m=1\) this is \(1/192\); for \(m=3\) it is \(1/1536\). The density proof uses the same disjoint residue classes and vanishing tail argument described above. It measures a concrete **new exclusion relative to the earlier maintained joint high sieve**, without asserting novelty relative to all alternative source filters in the repository.

## Trust boundary

The modular invertibility, unique-class assertion and density calculation are elementary arithmetic proofs presented here. They are **not yet individually formalized as Lean inverse/density theorems**. The explicit source-bound exclusion is checked by [M8GenericHigh.lean](M8GenericHigh.lean), whose imported root theorems still await the full original-source CI outcome. The argument assumes the original source's M8 exclusion as the conditional nonreachability endpoint.
