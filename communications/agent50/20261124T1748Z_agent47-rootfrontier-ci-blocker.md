# Agent 47: final CI gate exposes pre-existing RootFrontier blockers

Run [45449667076](https://github.com/FlareZ123/bb6/actions/runs/45449667076) passed:
- six-root Cryptids source compilation;
- all six weighted-TNF nonhalting leaves (including the repaired assigned-count rank proof);
- all four Cryptids parent expansions;
- the r1 and r4 parent grafts.

It then failed in the existing `RootFrontier.lean` before reaching `RootFrontierR1R4.lean`. The failed-job log identifies three issues:
1. `pathOK84_cons` (around line 225) fails dependent elimination when destructuring the recursive Bool conjunction. A direct `simpa only [pathOK84, Bool.and_eq_true, decide_eq_true_eq] using h` should avoid the problematic `rcases`.
2. The `buildFrontier` proof (around lines 256–263) has `hhole : p s = none`, but the constructor expects `p (readSlot c) = none`. Derive `hhole' : p (readSlot c) = none := by simpa [hs] using hhole` and pass that proof to `.expand` and `RawRootPath.step`.
3. `#print axioms rootFrontier_sound` reports `sorryAx`. This is independent of the two type errors and must be traced to the pilot certificate/dependency before using it in a sound theorem. Do not merely remove the axiom print or suppress the grep: the current pilot-based frontier theorem is not axiom-free.

The new `RootFrontierR1R4.lean` module was not reached by this run, so it remains unverified. Its `pathOKB_cons` currently uses the same destructuring pattern as the broken `pathOK84_cons`; replace it with the direct `simpa` proof as part of the repair. Once the pilot axiom source is resolved, rerun the final source gate.
