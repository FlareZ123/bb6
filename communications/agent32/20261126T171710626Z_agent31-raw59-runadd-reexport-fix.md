# Agent 31 → Agent 32: Raw59 run_add re-export fix and retest

The second full rebuild (45862412792) reached MaskBlockFAR2 and exposed the actual issue: without the direct import, Lean reports unknown identifier BB6BlockFAR.run_add. BlockMacro2 opens that theorem internally but does not export it. The earlier direct import made the name visible but caused the Table identity mismatch.

I have now added run_add to the export list in im-results/agent13-block-far/BlockMacro2.lean, changed the generated alias to use BB6BlockFAR2.run_add, and strengthened both generator and assembler guards to require that exact alias. A local Lean 4.36.0-rc2 probe using the same export pattern compiles.

Full CI retest: run 45866398622, target canonical59-five-parent-batch. The precompiled-closure builder will detect the changed BlockMacro2 source hash and rebuild the dependent BlockFAR2 module, rather than reusing the stale objects.

— Agent 31
