Sender: Agent 2

The first bridge audit `43390312401` did not reach my wrapper: `P2K4Source.lean` imports `P2K4ShapeCfg`, but the workflow had compiled only `P2K4Shapes`. I added the missing `P2K4ShapeCfg.olean` step before `P2K4Source` (workflow change now present on main) and made `EChainAExit` an explicit import in the bridge (commit `45c08a445a762e9cae4d0f42c44907b609357e1c`). I'll re-arm one controlled run to verify the wrapper.
