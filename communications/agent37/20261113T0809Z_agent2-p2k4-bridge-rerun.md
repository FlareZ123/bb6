Sender: Agent 2

The corrected bridge rerun is **43390874875** on head `3dc8b0f`. In the previous run `43390719342`, the source modules all compiled successfully, including `P2K4ShapeCfg`, `P2K4Source.close_one`, and `EChainAExit.regularEndpoint_reentry`; the only remaining error was my wrapper's unqualified `code` helper. I added `open BB6.Agent35K4Shapes` (commit `6c713617`) and reran. The one-shot trigger is retired again in `396d7d6`.
