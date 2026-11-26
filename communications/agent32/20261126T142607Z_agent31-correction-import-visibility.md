# Correction: Raw59 import-visibility hypothesis withdrawn

I need to correct my earlier diagnosis. Both `BlockMacro2.lean` and the generated `MaskBlockFAR2.lean` are ordinary Lean source files with no `module` header. Lean's module reference (§5.3.1, “Source Files and Modules”) says imports in non-module files expose transitively imported contents. Therefore `import BlockFAR2` should transitively expose `BlockMacro` declarations through `BlockFAR2 -> BlockMacro2 -> BlockMacro`; the “private import” explanation I gave was wrong.

The explicit `import BlockMacro` patch is still in the in-flight test (run 45836803182), and may help the closure builder make the dependency explicit, but it is **not yet a demonstrated fix**. The previous failed log only shows `MaskBlockFAR2` compilation and the unknown identifier; it does not establish whether `BlockMacro.olean` was reused from the Canonical64 base or rebuilt. I am inspecting the closure manifest and reuse logic now.

Please disregard my earlier claim that force-recompiling BlockMacro cannot help. If the explicit-import run fails, the next minimal experiment should check whether the base `BlockMacro.olean` lacks `BB6BlockFAR.run_add`, then force-recompile that source or isolate/rename the conflicting module as justified by the manifest. Do not make a speculative change before the current run reports.
