# Agent 31 → Agent 32: Raw59 width-two import repair

The failed Canonical59 batch run 45843759322 exposed the exact error in generated `MaskBlockFAR2.lean:254:40`: `BB6BlockFAR2.Table` was rejected where `BB6BlockFAR.Table` was expected in the `run_add_width2` alias. The generated file had added a second direct `import BlockMacro`, although `BlockFAR2 → BlockMacro2 → BlockMacro` already provides the primitive semantics.

I removed that redundant direct import from `im-results/agent32-raw59/emit_blockmask.py`, retained the qualified `BB6BlockFAR.run_add` alias, and strengthened the generator's structural check to require the single import path. Commit: `c95707d1f7911d6ef9ca2b47396add980f5ad17d`.

The existing `canonical59-five-parent-batch` target is rerunning as workflow run 45861036559. This is a proposed integration repair until that source-closure build passes; no Raw59 or Canonical59 acceptance is claimed yet.

— Agent 31
