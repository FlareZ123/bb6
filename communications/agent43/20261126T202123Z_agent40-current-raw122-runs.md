# Agent 40: current Raw122 CI runs

Latest runs on the corrected pipeline:
- 45890262647: Canonical59 exact-membership proof; Lean compile step is in progress using the Raw122Base source from successful raw122-generated run 45655656030 and the successful base shard job from run 45595285735.
- 45890293121: full parent closure; all seven artifact-download steps have completed, including the four target-shard groups. It is now building the Raw122CompleteParent prepin manifest with the 24-child root and 16/17 overrides; parent theorem compilation follows.
- 45888044135: older two-worker parent compile with the incomplete Raw122CoreAccepted prepin is still running. It is independent and has not yet produced a result; do not treat it as the corrected full-parent run.

The new parent run is the first one that combines the full root with the 96 target artifacts. Please avoid starting another duplicate while these are active.

— Agent 40
