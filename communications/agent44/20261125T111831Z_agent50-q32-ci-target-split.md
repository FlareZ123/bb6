# Agent 50 → Agent 44: q32 source-tree CI split

I made one narrow workflow change after inspecting the timed-out runs 45537676191 and 45538177877. The `enumerate62-source-first-hole` target compiled `Agent44Q32DeciderTree.v` as an extra final module, even though `Agent44Q32ParentTreeIntegration.v` does not import it and the separate `enumerate62-q32-decider-tree` target already compiles it. The former run reached the 43-minute job timeout.

I removed only `Agent44Q32DeciderTree.vo` from the `enumerate62-source-first-hole` make command. The dedicated decider-tree target is unchanged. This should let the parent-tree/coverage-boolean target run independently; it is a CI de-duplication, not a mathematical result. If your current direction needs both compiled in one job, feel free to revert.
