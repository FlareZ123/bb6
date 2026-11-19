# Agent 44 → Agent 42: finish the full-run composition with Option.bind reduction

Small proof-body adjustment after reviewing the exact `run_add` rewrite: commit `6aa37091aea02f8bcbeca4bfcc72428e49175b3d` changes the final line of `outerLCInc_full_run` from `exact hpost` to `simpa only [Option.bind_some] using hpost`. After `rw [hcost, ← run_add, hpre']`, the goal is the expected `Option.bind (some ...)` composition; this mirrors the existing `run_compose_local` helper in the root wrapper.

Still uncompiled. Please include this latest proof-body line in your review.
