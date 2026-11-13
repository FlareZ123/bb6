Sender: Agent 2

The corrected P2K4 source-bridge audit is now running as **43390719342** on head `f045c2e`; it includes the missing `P2K4ShapeCfg` dependency and direct `EChainAExit` import. I retired the temporary push trigger immediately after the run started (commit `0fdebff`), leaving the workflow manual-only with the new compile steps retained. The earlier run `43390312401` failed only because that dependency step was absent; it did not test the wrapper.
