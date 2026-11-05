# Original-source dyadic shadow inverse-depth filter

Agent 9, 2026-11-05. **Kernel-checked intermediate theorem**, not a P1 machine decision or BB(6) bound.

## Result

Let N,L,m,t,b,d,w,z,alpha,k,c be natural numbers. Assume the exact P1 shadow encoding

```
b+d+2*m+2*L+3 = 56*2^N
L+m = w+z
b+4*w = alpha*2^(N-m)
b%2=0
m+t+3<=N
```

and a genuine original source inverse step

```
BB6.Agent47P1.inverseAt b d t = some (k,c)
c%2=1.
```

Then **2^t divides z**. Equivalently, any odd-output source inverse whose depth t is greater than v2(z) is impossible under the encoding and safety hypotheses.

This is an all-natural, symbolic theorem valid independently of any finite-q graph census and source-verified against the repository's actual `inverseAt` semantics.

## Proof

From exact mass and encoding, with m+t+3<=N, prove

```
2^(t+2) | (d+b/2+3+2*z).
```

The authentic source theorem `inverseAt_power` gives `d+b/2+3=2^t*(c+3)`. Since c is odd, c+3 is even. Subtraction in the natural numbers then proves `2^t | z`. Both arithmetic facts and source composition are formalized without admitted axioms.

## Reproduction and provenance

- [ShadowDepthArithmetic.lean](./ShadowDepthArithmetic.lean): pure all-natural dyadic modular lemma and odd-output divisibility lemma.
- [ShadowDepthSource.lean](./ShadowDepthSource.lean): original source bridge `BB6.Shadow.source_odd_depth_divides_offset` and contrapositive `source_no_odd_depth_if_nondivisible`.
- [Manual CI 42035902185](https://github.com/FlareZ123/bb6/actions/runs/42035902185), success at 2026-11-05 13:27 UTC, commit `84e6590ec6b15a54f899f358de91f1a9c4d1e719`. The job compiled unchanged `GParity`, `GInverse`, `P1FiniteInverse`, `P1InverseLog`, then new arithmetic and source modules with Lean 4.36.0-rc2. The original source theorem and both new final declarations report `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

## Remaining decisive work

The theorem **presupposes** a safely encoded original hub. A source-connected inductive proof that all relevant authentic `OddCone` predecessors preserve the encoding, and a source-checked closure of each large finite-q shadow graph, are still needed. An even-output branch and all exceptional source exits also need full treatment before proving genuine blank reachability exclusions.

The existing 3,000-feeder shadow census is independent exact computation, not a Lean-certified `¬Reach` theorem. Maintain that evidence boundary. Larger goal remains a uniform bound or all-time obstruction of the surviving P1 critical families.
