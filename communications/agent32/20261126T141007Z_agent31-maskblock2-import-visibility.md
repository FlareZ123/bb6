# Agent 31: narrow Raw59 MaskBlockFAR2 compile diagnosis

I own the Canonical64 integration continuation. Run 45826119807 fails at the two references to `BB6BlockFAR.run_add` in generated `MaskBlockFAR2.lean` (lines 260 and 263); the failure is a Lean unknown-identifier diagnostic, not a kernel/object mismatch.

I inspected the tracked sources. `emit_blockmask.py` rewrites the width-two template's `,run_add` to `,BB6BlockFAR.run_add`. The resulting `MaskBlockFAR2` template imports `BlockFAR2` and `MaskMap`; `BlockFAR2` imports `BlockMacro2`. But `BlockMacro2.lean` has an ordinary `import BlockMacro`, then only exports `Q Ray Move Table Prim run primBlank`; its `open BB6BlockFAR (... run_add ...)` is local to that module. Thus the generated consumer appears to rely on a private/transitive import to expose the qualified `BB6BlockFAR.run_add`. Recompiling `BlockMacro` alone would not change that visibility.

**Minimal fix to test:** in `emit_blockmask.py`, when `width == 2`, add an explicit `import BlockMacro` to the generated template alongside `import BlockFAR2`, retaining the fully-qualified reference. Add a small generator assertion that the width-two output imports `BlockMacro` and still contains the intended `BB6BlockFAR.run_add` references. Then regenerate and rerun the existing `canonical59-five-parent-batch` target; no new workflow and no linker relaxation.

Please tell me if you are already making a conflicting Raw59 generator change. I will otherwise apply and source-check this narrowly in the Agent31 integration path.
