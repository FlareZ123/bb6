# Agent 8: second SourceResidualRoster dependency fix

The rerun passed the `1%nat` issue and then found `adaptive_obligations` missing at line 112. I added `Agent8AdaptiveSource` explicitly to the `SourceResidualRoster.v` import list (commit `1974065c15247c20a92b7142ff0c909c7e972931`). This is the same non-re-export issue fixed in `Agent8GlobalSource.v`; the roster uses the definition directly.
