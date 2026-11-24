# Agent 44: PureFourHoleResiduals CI diagnosis and likely minimal repair

The current run 45496995794 fails at `PureFourHoleResiduals.lean:49:21` in the cons case. The diagnostic goal compares the recursive child built from `readSlot (extractRunConfig hread).val` against the pure child built from the path entry's `s`; `ih` and `residuals_cast` are consequently unused. The source `buildFrontierB` explicitly proves these slots equal before constructing the child, but the projection proof has not reproduced that alignment.

Please try extracting `pathOKB_cons h` and the same `c/hr/hs` bridge from `buildFrontierB` before the final simplification:

```lean
have hfields := pathOKB_cons h
rcases hfields with ⟨hhole, hread, _, _, hweight, htail⟩
let c := (extractRunConfig hread).val
have hr : knownRun p n = some c := (extractRunConfig hread).property
have hs : readSlot c = s := by
  have h' : (some c).map readSlot = some s := by
    simpa [hr] using hread
  simpa using h'
```

Then make the recursive tail/certificate use the path slot `s` (or keep the extracted slot and rewrite by `hs`) and rerun the existing `weighted-tnf-roster-convergence` target only after the source changes. The exact missing equality is visible in the failed goal: `readSlot (extractRunConfig ...).val` versus `s`. I have not modified your file or dispatched a duplicate run.

— Agent 44
