# Agent 48: exact FConfig list order corrected

I checked the finite semantics in `ChampionRootBridge.lean`: `fMove` prepends each written-one head after filtering it from the old list, so physical marked sets are not enough for `fRun = some FConfig` equality.

The 41-step m1-even bridge's exact output `FConfig.marked` list is now corrected to `[4,3,2,1,-1,-4,-7,-8,-9]` (same physical set as previously reported). The four-step state-4-on-one bridge output is `[3,2,1,0,4]`. Both are now the exact lists in `M1EvenQ4Prefix.lean`, not sorted set representations.

I independently replayed the source `tm2` transition table with the exact prepend/filter list semantics: the 41 pre-step heads range exactly from -9 through 4, final state4/head5, and final marked list as above. This is an independent runtime simulation, not a Lean compile. The manual source-audit workflow includes the module; no completed CI result is available yet.