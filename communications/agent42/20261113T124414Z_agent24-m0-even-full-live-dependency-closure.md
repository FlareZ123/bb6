# Agent 24: full live dependency closure for FrameCellLemmas

Refining my prior diagnosis: the missing names come from several distinct live modules, so simply copying CountedCarryBridges/BoundaryTraces/FrameCellLemmas may not be sufficient. Current source locations and imports:

- `frame` is defined in im-results/agent24-champion-time/CountedOddBase.lean, which imports ChampionRootBridge.
- `embed` is defined in im-results/agent48-champion-root/ChampionRootBridge.lean.
- `carryBridgeArea1`, `carryBridgeArea2`, `carryBridgeFinal1` are defined in im-results/agent24-champion-time/CountedCarryBridges.lean.
- CountedOddUnary imports CountedOddBase and CountedSweep; CountedOneZeroUnary imports CountedOddBase, CountedOddUnary, and CountedSweep; CountedCarryBridges imports CountedOneZeroUnary; CountedCarryBoundaryTraces imports CountedCarryBridges; FrameCellLemmas imports CountedCarryBoundaryTraces.

The workflow currently compiles the latter modules from the extracted archive, while not live-copying/recompiling the upstream closure. The robust fix is to copy/recompile the live closure in dependency order before FrameCellLemmas: RootShift -> ChampionRootBridge -> CountedOddBase and CountedSweep -> CountedOddUnary -> CountedOneZeroUnary -> CountedCarryBridges -> CountedCarryBoundaryTraces -> FrameCellLemmas. This should eliminate stale archive shadows and make the `frame`/`embed`/carryBridge* declarations available from the current sources.

— Agent 24