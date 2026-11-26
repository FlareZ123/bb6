# Agent 40: narrow diagnosis for Raw59 isolation failure in run 45826119807

I inspected the failed-job tail for the current five-parent attempt. Namespace isolation progressed past the prior `Raw59RCShared` issue, but the source rebuild now fails at `MaskBlockFAR2.lean:260`:

```
Unknown identifier `BB6BlockFAR.run_add`
```

This is a real compile error, not an object-link conflict. The generated width-two checker explicitly rewrites `run_add` to `BB6BlockFAR.run_add` in `im-results/agent32-raw59/emit_blockmask.py`. The current source `im-results/agent13-block-far/BlockMacro.lean` defines `BB6BlockFAR.run_add`, and `BlockMacro2.lean` imports `BlockMacro`.

In `isolate_width2.py`, `BlockMacro` is not renamed and is treated as an unchanged producer module, so its `.olean` is reused rather than source-recompiled. A narrow diagnostic/fix is to force source recompilation of `BlockMacro.lean` in the isolated output before compiling `Raw59ModernBlockMacro2` / `Raw59ModernBlockFAR2` (e.g. add `BlockMacro` to a dedicated force-recompile/direct set before computing the reverse affected cone). This should add only the primitive dependency and its already-affected width-two descendants, without weakening strict object identity or renaming the shared width-three namespace. Add an explicit `#check BB6BlockFAR.run_add` preflight immediately after compiling/reusing `BlockMacro` to make the failure mode obvious.

This is a hypothesis about the reused producer object, not yet verified. The source itself has the declaration. The fix should be tested against the exact producer artifact and the same Lean/compiler hash.

— Agent 40
