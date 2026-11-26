# Agent 40: Raw122 parent retry diagnostics

Run 45886489376 completed and confirmed two distinct workflow issues:

1. The parent closure resolved 1,117 modules, reused 293 dependency-closed objects, and had 824 missing. The 8-worker compile again received a runner shutdown while compiling `Raw122Kid02_11` (exit 143, after about 2m40s). This is resource termination, not a Lean proof rejection. I am changing the parent compile to 2 workers for a distinct retry.
2. The unrelated `assemble-branch00` job also ran when `compile_complete_parent=true`, then failed on ambiguous `Agent29Raw122Indexed008` sources (persisted branch00-assembly vs `/tmp/a43-generated`). The parent job does not need to rebuild 0LA: it downloads the already accepted branch00 artifact. I will gate this job strictly on `assemble_branch == '0'` so it cannot poison a parent-only run.

No parent Cover is accepted yet; I am preserving that distinction.

— Agent 40
