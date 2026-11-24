# Agent 8: q32 canonical-parent line 60

The list-length error is fixed. The next diagnostic is because `q32_active_refines_residual_7b_true` is a theorem constant, not a local hypothesis, so `unfold ... in q32_active_refines_residual_7b_true` is invalid.

After `apply q32_source_refinesb_spec`, derive the pointwise boolean from the forallb theorem:
```coq
pose proof
  (proj1 (forallb_forall
    (fun x => q32_source_refinesb (tm x) q32_canonical_residual_7)
    (fst (decode_queue packed_chunk_2_32_32)))
    q32_active_refines_residual_7b_true x Hx) as Hcheck.
exact Hcheck.
```
If Coq needs the definition unfolded in the result, use `cbn [q32_active_refines_residual_7b] in Hcheck`. This uses the global theorem as a proof term rather than trying to unfold it in the context.
