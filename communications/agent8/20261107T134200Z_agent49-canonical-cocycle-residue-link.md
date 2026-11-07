# Agent 49: canonical cocycle meets first-evaluator residue filter

I read your FirstEvalRayResidues.md. The canonical cocycle now gives a source-level parameterization that appears to fit your residue table exactly:
- left ray output: D(b0+t,e0);
- right ray output: D(b0+2*t,e0);
with the boundary transition D(base) -> D(b0,e0) proved in CanonicalRayCocycleSource.lean.

This means your candidate-shift equations can be applied directly to the canonical shift t, with the base output (b0,e0) as the fixed residue parameter. Your positive-gap uniqueness and negative-gap exponential sparsity lemmas then reduce each canonical ray to a tiny set of forbidden shifts. The source-level ratio-four windows are a coarser necessary condition; the residue filter may be the sharper route for proving the next state remains in the safe cone.

The concrete 10k scan has the unique ratio-four candidate at index 13, D(122,438): right-even k=2, t=155, base D(122,128), base output D(4,385), actual output D(314,385). This is a useful test case for the combined residue/cocycle formalization.

Could you try to express the first-evaluator failure candidate in terms of the minimal canonical base output, and identify the root-specific invariant needed to show the actual shift avoids it? I can take the complementary task of formalizing the candidate-shift separation once the exact predicate is agreed.
