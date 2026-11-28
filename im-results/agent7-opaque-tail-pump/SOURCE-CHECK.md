# D100 hard frontier: original-source local kernel check (2026-11-28)

All three formerly persistent 300m-step literals have actual Lean 4.36.0-rc2 theorems in the repository's original infinite-tape semantics. This is a local source check, not a claim that a new CI run occurred or that the parent Cover has been accepted. The compiler was reconstructed from the two uploaded ZIP parts. Original imported sources were fetched via GitHub connector and locally checked byte-for-byte by Git blob ID. Compile these dependencies in order, with LEAN_PATH pointing to the directory containing their .olean files.

| Module | Git blob |
|---|---|
| Frontier | 115438c4f244b5416a91be4dd7a3f12103d5448d |
| Symmetry | 84f62dcea34e7f2a97d07016cc2d9065d4ddd7ce |
| RootShift | 80b56fb040f7db81277fcf52cd43e6127fe365ba |
| SparseZipper | 8081dc82ca1e892ab2f6c698d94b6dc24129f6e6 |
| SweepPumping | e518c288ecdf5c96890ad64b5971f5c2f18a2106 |
| BlankDelayKernel | 1cbc53f53e9d8329545b1737ae137e142aed2e65 |
| FirstStep | 158b7f35a165a4cda2cc42d7d8524cc8ed6af4f3 |
| WriteOneDrift | fa449e911de622670e7ee88889dfe81148ecf31e |
| BlankDelaySource | 515b137f7307b3828285aa1acabd0308c85c3cfb |
| SparseBlankDelay | 37457de22d117eed0a8f0059cc28cae6f0c3bfb0 |
| D100UnaryDouble | 6abe2d4c18cf20479b27a21cf4175c133bd28f74 |
| D100Countdown | d8e489893d28ffdff00a2971e95b116f08ab9662 |
| D100CountdownNever | ff0694489604ef46a957371d462d2a132d5c7fb2 |
| D100Delayed | eb35dcc39003d1b609e2414153a2f4bc728fcfd3 |
| D100DelayedTrace | 1e87b2456cbf3a20055fe4ead188e4f18c14a77a |
| Run0LastHole | 0dc606e49e4d8b1c02ffa66632253cd855296ab2 |
| D100DelayedBound | ef9f2a8caad01ba79363e71819522920890926de |

Root outputs, with no sorryAx or ofReduceBool or native_decide:

```
'BB6.Agent7D100UnaryDouble.never' depends on axioms: [propext, Quot.sound]
'BB6.Agent7D100Countdown.never' depends on axioms: [propext, Quot.sound]
'BB6.Agent7D100Delayed.reached' depends on axioms: [propext, Quot.sound]
'BB6.Agent7D100Delayed.hole' depends on axioms: [propext]
'BB6.Agent7Run0LastHole.halter_exact' depends on axioms: [propext, Quot.sound]
'BB6.Agent7Run0LastHole.bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent7D100DelayedBound.bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The delayed certificate now uses a smaller direct bridge, Run0LastHole. This avoids evaluating either the massive run or the sparse delay graph, and requires only SweepPumping and SparseBlankDelay. The general bound theorem uses source kernel `terminal_delay_le_five`; any halting completion must halt at the reached slot, because assigning that slot a normal move produces a completely nonhalting table. No other one-hole literal is assumed to behave this way unless its run0 prefix and all remaining ordinary rows are proved. D100Delayed line 168 is corrected to normalize U 1 explicitly; the checked source matches the original reconstructed proof blob.

Parent assembly still needs literal-bank integration and accepted parent Cover. No global residual count change is asserted here.

## Final F1 exposure

`D100FiniteF1.lean` blob `3abafd56a971aa7dbacbab9cc340acb7a9531e0c`; `D100FiniteF1Trace.lean` blob `5f8d39eaa8b9015f40cd1691561a2393f924a26b`. Compiled with the same original-source closure and Lean 4.36.0-rc2. `BB6.Agent7D100FiniteF1.reached` axioms `[propext, Quot.sound]`; `BB6.Agent7D100FiniteF1.bound` axioms `[propext, Classical.choice, Quot.sound]`. Exact first query F1 after 4672258 transitions, weighted bound 4672264. No `sorryAx`.
