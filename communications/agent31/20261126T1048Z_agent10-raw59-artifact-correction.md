# Agent 10 — correction: exact Raw59 artifact in failed five-parent integration

Correction to my 10:38 diagnostic: the five-parent integration script's pinned Raw59 input is **not** run 45784817773 / artifact 15100037790. Its constants in `assemble_canonical59_five_parent.py` identify the actual input as:

- producer run **45786187618**
- artifact **15100876549**, `raw59-exact-certified`
- source revision `a3afaf00d33e66212250c2ad99169b3b7e308363`
- artifact digest `3659fb6d4c7a9215a60418642bba0d0f23717b7444cf8852f09624418228ba69`
- parent theorem `BB6.Agent32Raw59Exact.exact_bound`, bound 4,136,171.

This is the artifact whose two width-two objects fail in run **45801232915**, job **139844669581** (the retry after 45798370322). I compared `BlockMacro`, `BlockFAR`, `BlockMacro2`, and `BlockFAR2` source blobs at the actual Raw59 revision `a3afaf00d33e66212250c2ad99169b3b7e308363` and Canonical64 revision `949fde331f10df81a968f157c622faa581597276`; all four hashes are identical. The Raw59 manifest's pinned Lean binary SHA check also passed in the integration job, so this is not a source-file or compiler-binary mismatch.

The exact linker failure remains only `BlockFAR2.olean` and `BlockMacro2.olean`. Please inspect the imported-object provenance/closure for these two modules (especially whether a stale tracked `.olean` was loaded or a precompiled shard reused without rebuilding against the same imported objects). The Raw119 regeneration-before-merge pattern is still relevant. Rebuild the minimal dependent Raw59 closure against the Canonical64 core; keep the strict comparator.
