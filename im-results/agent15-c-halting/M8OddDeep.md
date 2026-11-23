# Explicit deep M8-excluded Machine C stopping families

**Status:** Mathematical construction plus Lean 4.36.0-rc2 source-body preflight, using signature-compatible import stubs. The entire original Machine C dependency graph has **not** yet been recompiled with these new modules. This is an intermediate result, not a BB(6) solution.

## Arithmetic family

For every **odd** positive integer \(m\) and every \(t\ge0\), put
\[
 B=2^{2m+2},\quad Q=(B-1)/3=1+4+\cdots+4^m,\qquad
 T=\begin{cases}15+16t,&m\equiv1\pmod4,\\5+8t,&m\equiv3\pmod4.\end{cases}
\]
Define
\[
 j=(B-3)(m+1)+BT,\quad
 N=(Q-1)m+Q(T+1),\quad k=3BN-2.
\]
The exact high stopping equation follows from \(3Q+1=B\):
\[
 k+j+3m+5=B(j+3).
\]
Moreover, \(Q\equiv5\pmod{16}\), hence
\[
 \begin{array}{c|c|c}
 m\bmod4 & N & d=\operatorname{oddDepth}(k)\\
 1 & N\equiv4\pmod{16} & 2m+3\\
 3 & N\equiv2\pmod8 & 2m+2
 \end{array}
\]
In each case there is a positive \(v\equiv2\pmod8\) such that \(k+2=3v2^d\). The original affine-normalizer stopping theorem then forces \((p_2+2)/3\equiv2\pmod8\). Also \(j\) is even, \((j+m)\equiv3\pmod4\), and \(2d\equiv m+1\pmod4\). The source M8 exclusion therefore gives
\[
 \neg\operatorname{CReach}(2j+3,k).
\]
Thus this produces an explicit infinite progression of *forbidden second-stopping inputs* for **each odd m**, in the full deep-normalizer sector.

The progression step in \(j\) is \(16B\) for \(m\equiv1\pmod4\) and \(8B\) for \(m\equiv3\pmod4\). Base examples \((m,j,k,d)\): \((1,266,4030,5)\), \((3,2292,585214,8)\), \((5,85998,352174078,13)\). These are not blank-run halting witnesses.

## Non-overlap with the earlier dyadic tower

Here \(j+3m+3=B(m+T+1)\). Therefore for every \(n\) with \(n+4\le2m+2\),
\[
 (j+3m+3)\bmod2^{n+4}=0\ne2^{n+2}.
\]
This avoids the pair-residue condition of the earlier all-depth tower sieve. The pure arithmetic proof is `deep_prior_tower_avoided` in the Lean source.

The shallow alternatives in [M8AllOddExplicit.lean](M8AllOddExplicit.lean) and [M8OddDense.lean](M8OddDense.lean) have depth 1 or 2 and **overlap the earlier tower sieve**. They are retained as constructive arithmetic scaffolding, not claimed as an independent improvement. The deep construction is the useful new comparison target.

## Reproducible formal content

- [M8UniversalAlgebra.lean](M8UniversalAlgebra.lean) and [M8AllOddExplicit.lean](M8AllOddExplicit.lean): geometric algebra and shallow base construction.
- [M8OddDeepAlgebra.lean](M8OddDeepAlgebra.lean): general high-family stopping equation.
- [M8OddDeep.lean](M8OddDeep.lean): `deep_every_odd_unreachable`, `deepIndex_step`, `deep_prior_tower_avoided`.
- [M8OddDense.lean](M8OddDense.lean): dense shallow control family, superseded for novelty.

All these newly developed proofs compiled locally on Lean 4.36.0-rc2 with no `sorryAx` when the previously certified source theorems were represented by *exact-signature test axioms*. The displayed axiom profile of `deep_every_odd_unreachable` includes those imported-source assumptions. For a fully source-certified result, compile the real modules after `DeepSecondFinal`, `AffineQuotientExclusion`, `M8FilteredResidual`, and `M8SharpFamily` using the original-source workflow.

**Research boundary:** Excluding these stopping inputs is strictly weaker than ruling out every infinite high-family parameter. No claim that Machine C never halts or that BB(6) is determined follows.
