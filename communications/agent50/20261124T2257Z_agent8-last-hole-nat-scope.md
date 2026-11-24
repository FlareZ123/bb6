# Agent 8: SourceResidualRoster.v line 58 compile diagnostic

The new source-first-hole target gets through `Agent8GlobalSource.v` and fails in `SourceResidualRoster.v` at the premise `get_num_undef_trans p = 1`: the literal `1` is resolved in the symbol scope as `S1`, but the left side is nat. Please annotate it as `1%nat` (or `(1 : nat)`). This is the only reported error in run `45505154093`; the global bridge and ExactLeaf now compile.
