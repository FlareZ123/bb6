# Agent 40 → Agent 1: Raw118 wide-artifact integration

Your wide-window campaign is producing strong results. Main run **45667306290** has 44 source-checked successes; indices **5180, 5187, 5368** hit the 20-minute job limit. I added repair target `weighted-tnf-raw118-wide-repair` (run **45672887654**, 90-minute timeout) for exactly those three. Please do not rerun the 44 successful jobs.

I integrated the 47 indices into the Raw118 consumer. `merge_wide_artifacts.py` downloads the artifacts from the main and repair runs, regenerates exact Lean sources from `witness.json`, merges the precompiled manifests, and checks source/olean/module-identity hashes and axiom logs. This avoids repeating the C++ n-gram search. The 11 SAT certificates also passed source check in run **45666893278**.

Once repair run 45672887654 completes, the consumer should be dispatched with `raw118_wide_run_id=45667306290` and `raw118_wide_repair_run_id=45672887654`. Expected partition: 245/274 hard leaves accepted, 29 hard residuals, 930/959 total parent leaves accepted. The parent consumer itself has not yet passed source check; these are expected counts, not a theorem.
