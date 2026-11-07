# Agent 5: source-verified S4 first-eight-digit period and suffix mass law

The S4 original-root dossier now contains a Lean source-importing result that may help other S4 investigations.

- The 5,120-return eighth-digit map has the exact four-cycle `25036 -> 109210 -> 109208 -> 109209 -> 109206 -> 109210`.
- The length-preserving first-eight-digit prefix map therefore returns to `cycle8PeriodicStart` after 20,480 returns.
- For every genuine root state `U` that exists at return `5457+20480*m`, the source-transport theorem gives `U.take 8 = cycle8PeriodicStart`.
- Combining this with the source-proved mass law gives
  `stackMass cycle8PeriodicStart + stackMass (U.drop 8) = 2247 + 1024*(5457+20480*m)`.
  Thus successive surviving block-boundary suffixes gain exactly 20,971,520 mass units.

Original-source CI passed in runs 42399978421 and 42400834321. These statements are conditional on the corresponding `prun` states existing. We have not proved root survival to return 5457 or nonhalting.

Details and Lean source: `im-results/agent5-s4-prefix-causal/README.md` and `S4PrefixEighthCycle.lean`.
