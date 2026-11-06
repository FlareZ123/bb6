# Machine C: valuation-controlled exact source indegree

**Result and scope.** For any target \((x,y)\) of the original Machine C first-return section with \(y\ge5\), let \(S=x+y\), and define \(V=\nu_2(S)\) when \(S\) is even, and \(V=\nu_2(S+1)\) when \(S\) is odd. The exact number \(d(x,y)\) of distinct immediate original-section predecessors obeys

\[
d(x,y)\le \lfloor V/2\rfloor+1.
\]

This bound is **sharp for every integer \(V\ge3\)**: when \(V\) is odd use \((x,y)=(2^V-5,5)\), and when \(V\) is even use \((x,y)=(2^V-6,6)\). In both cases the indegree is exactly \(\lfloor V/2\rfloor+1\). The source-map property is distinct from any claim of authentic blank-root reachability. **Machine C and BB(6) remain undecided.**

**Proof status.** The valuation/divisibility/parity core is locally Lean 4.36.0-rc2 kernel checked, and [ValuationSource.lean](ValuationSource.lean) is **unmodified-original-source checked**, in [successful manual CI 42196982230](https://github.com/FlareZ123/bb6/actions/runs/42196982230), with standard axiom audits. The final global cardinality and all-\(V\) sharpness assertions are presented below as a **written mathematical derivation** using Agent 3's already source-certified exact predecessor if-and-only-if. A separate Lean theorem for the cardinality/sharpness is not yet supplied; do not refer to those two statements as kernel-certified. The accompanying numerical checks test, rather than replace, that proof.

## Exact-source argument for the bound

The original [source map](../agent46-c-jump/FastSectionDef.lean) includes direct, exceptional, and recursive bounce cases. Agent 3's [section_preimage_all_iff](../agent3-c-bounce-inverse/SectionAllInverse.lean), certified by [CI 41544188316](https://github.com/FlareZ123/bb6/actions/runs/41544188316), is an exhaustive **iff** for every source and target. Restrict to \(y\ge5\).

If \(S=x+y\) is **even**, any high-input source has even first counter \(a\ge2\). Its recursive depth \(n\ge0\) satisfies

\[
 S=2^{n+1}(a+2),\qquad
 2k+a+7+3n=x+2y.
\]

Because \(a\) is even, \(2^{n+2}\mid S\), and the second equation forces \((n+1)\bmod2=x\bmod2\). Thus \(0\le n\le V-2\), only one parity of \(n\) is permitted, and each \(n\) determines at most one \((a,k)\).

If \(S\) is **odd**, a high-input source has odd \(a\ge3\) and satisfies

\[
 S+1=2^{n+1}(a+3),\qquad
 2k+a+7+3n=x+2y.
\]

Now \(2^{n+2}\mid S+1\), \(n\bmod2=x\bmod2\), and again each permitted depth determines at most one source. Both statements and both parity restrictions are source-connected theorems in [ValuationSource.lean](ValuationSource.lean).

For \(S\) even, an exceptional \(a=0\) source can exist only if \(S=8\cdot2^n\), requiring \(x\bmod2=V\bmod2\). For \(S\) odd, an exceptional \(a=1,k\ge4\) source can exist only if \(S+1=16\cdot2^n\), requiring \(x\bmod2=(V+1)\bmod2\). Each contributes at most one input. A direct source exists for every even \(y\ge6\) and is unique: \((a,k)=(S-2,(y-2)/2)\). The remaining special inputs \((1,2)\) and \((1,3)\) lead only to \((2,5)\) and \((0,7)\), respectively; those two targets have indegree one by the exact inverse equations.

## Parity count and constructive sharpness

The possible high-depth counts and the maximum other-source counts, respectively, are:

| S parity | V parity | x parity | High-depth count | Other source count |
| --- | --- | --- | --- | --- |
| even | even | even | V/2−1 | 2 |
| even | even | odd | V/2 | 0 |
| even | odd | even | (V−1)/2 | 1 |
| even | odd | odd | (V−1)/2 | 1 |
| odd | even | even | V/2 | 0 |
| odd | even | odd | V/2−1 | 2 |
| odd | odd | even | (V−1)/2 | 1 |
| odd | odd | odd | (V−1)/2 | 1 |

Here the other sources are the direct branch (only if y is even) and at most one a=0 (S even) or a=1 (S odd) exceptional source. The exceptional depths are uniquely V−3 or V−4, respectively, and require the indicated parity condition. Hence every row totals at most floor(V/2)+1. V=1 has no high or exceptional preimages and at most one direct source; V=2 is included in the table.

**Sharpness, odd V≥3.** Set (x,y)=(2^V−5,5). For each even depth n in [0,V−3], the source inverse equations give a genuine high-branch parent

```text
a(n)=2^(V−n−1)−2
k(n)=(2^V−2−a(n)−3n)/2.
```

An additional distinct exceptional a=0 source has k=(2^V+5−3V)/2. These yield (V−1)/2+1 actual parents.

**Sharpness, even V≥4.** Set (x,y)=(2^V−6,6). For each odd n in [1,V−3], the genuine source parent has the same a(n) and k(n)=(2^V−1−a(n)−3n)/2. Add distinct exceptional (0,(2^V+6−3V)/2) and direct (2^V−2,2) parents, giving V/2−1+2=V/2+1. The positivity and high-branch inequalities follow from the displayed formulas, the positive power-of-two difference for n≥1 and the elementary bound 2^V≥3V for V≥4; the odd V=3 base case is direct.

All parent constructions satisfy the source-certified if-and-only-if grammar, which supplies genuine transitions; separate numerical witnesses are unnecessary for mathematical existence.

## Reproducibility and significance

[valuation_fanin.py](valuation_fanin.py) independently implements the original recursive section interpreter and an arithmetic inverse oracle. Its finite regressions passed: 50,625 source pairs (49,844 successful y≥5 edges); 775,635 distinct targets with x+y<1250; every sharpness construction from V=3 through V=24. These computational checks support the paper proof and are not a substitute for universal source reasoning.

This is an all-target strengthening of the logarithmic candidate-slot bound in [Agent 11's inverse list](../agent11-c-bounce-exact/SectionFastInverseOriginal.lean); the current V-controlled bound can be tiny even for enormous targets. The exact unbounded family count at (0,16·4^t) from [Agent 3](../agent3-c-bounce-inverse/UnboundedInDegree.md) is a consistent special case. Originality relative to external research remains unassessed.

**Open obligation:** put the eight-case cardinality and all-V constructions into Lean itself, then exploit the new inverse budget to close an entire surviving *genuine blank-root* stopping branch. Even a sharp general inverse degree theorem is not a halt/nonhalt decision of Machine C and does not establish BB(6).
