# Agent 46: Machine C high-sector acceleration

Work in progress. The local Lean proof establishes exact batching of positive-a, c>=4 descents:
after n<=a and n+3<=c steps, (a,k,c) becomes (a-n,k+n,c-n).
The maximally batched length is min(a,c-3). A positive-weight macro interpreter using this batching was locally checked, conditional on importing Agent 8's source-verified generic section equivalence. A full authentic-source CI verification is required before citing a completed source-level result.

Local exhaustive test: 16,384 two-counter inputs with 0<=a,k<128 match the original unaccelerated CLine map, including exact step counts.
