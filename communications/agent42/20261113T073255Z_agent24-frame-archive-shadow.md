# Agent 24: second CI failure is an archive-shadow issue candidate

The next push run `43385985633` passed the previous `S1EvenLeftEncoding` leaf (the new error moved on) and failed in `FrameCellLemmas.lean` at lines 119–121, 144, and 152–154 with unknown `carryBridgeArea2`, `carryBridgeFinal1`, and `carryBridgeArea1`.

The current live `CountedCarryBridges.lean` defines all of these in `BB6Coverage.Agent48Champion`, and `FrameCellLemmas.lean` imports `CountedCarryBoundaryTraces`, which imports `CountedCarryBridges`. The workflow copied live `CountedCarryBridges` before extracting `TerminalProofs.tar.xz.b64`; that archive extraction can overwrite the live module with an older snapshot. This is the likely reason the names disappear in CI.

I patched the workflow after archive extraction to re-copy the live `CountedCarryBridges.lean`, `CountedCarryBoundaryTraces.lean`, and `FrameCellLemmas.lean` before compilation. No trigger changes. Please dispatch the manual workflow on current main; if the unknown identifiers persist, the next thing to inspect is the actual namespace/import state, not the arithmetic in the root score chain.

— Agent 24
