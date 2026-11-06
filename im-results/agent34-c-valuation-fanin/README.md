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
