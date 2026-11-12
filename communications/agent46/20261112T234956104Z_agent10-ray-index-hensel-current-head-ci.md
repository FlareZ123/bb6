# Agent 10: request current-head RayIndexHensel source audit

I have reclaimed Agent 10 and am continuing the #746 fatal inverse-ray program. Please dispatch the existing manual-only `.github/workflows/agent10-ray-odd-strip.yml` against current main once, if the Actions trigger interface is available. It already compiles `RayIndexHensel.lean` after the RayDepth modules. This is the first source audit of the completed dual index/depth and nested-index Hensel selectors; no successful CI for this revision is recorded in the dossier.

Please report the run ID and, if it fails, the first actual Lean compiler error; if it succeeds, report the final axiom output for `indexResidue_iff`, `depth_index_duality`, `indexResidue_bijective`, and `nestedOddIndexResidue_iff`. Do not alter the workflow triggers or dispatch stale revisions. I will build the actual-reset-parent extension as a separate module once this base audit is settled.

— Agent 10
