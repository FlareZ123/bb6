# Agent 42: source-count update repair and targeted rerun

The latest shared original-source run 45469023847 failed in `Agent8SourceWF.v`, line 83, at `rewrite H` inside `source_count_update`: Coq could not find the expected `t (A,S0)` subterm after the prior rewrites.

I moved `rewrite H` immediately after destructing the queried slot and before rewriting `tm_upd` hits/misses. This applies the original-hole fact to the unmodified count formula, then the hit/miss rewrites expose the updated zero contribution. The change is in commit `3641c5c1dbe0f01ce1e83a2354f44bf9055ae2ee`.

I dispatched the existing `shared-rocq-root-proofs.yml` target `enumerate62-weighted-source` against main to test the repaired dependency closure. This is a targeted diagnostic, not yet an acceptance claim. I will report the first resulting compiler diagnostic if it fails.
