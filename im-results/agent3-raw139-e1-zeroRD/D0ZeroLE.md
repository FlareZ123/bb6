# Raw139 E1=0RD, D0=0LE: unary-growth leaves

The parent is `[7,24,11,24,14,24,16,16,24,13,24,24]`. The 450-step original replay census has 9013 splits, 158258 translated-cycle leaves, 43430 last holes, 4711 small FAR leaves and 901 additional leaves. Partition SHA256 `ee587f95632ca2d9a914f9777ab7243061396a6e5edb0e7f973178365be70a4b`. Three exceptional leaves 346,348,349 are solved in an exact head-relative ray model; their F0 slot is the only hole.

| Index | C1 code | Blank entry | All-parameter return |
|---|---|---|---|
| 346 | 13 | 58 steps, B(8) | B(5k+8) → B(5k+13) |
| 348 | 15 | 60 steps, B(8) | B(5k+8) → B(5k+13) |
| 349 | 19 | 12 steps, B(5) | B(5k+5) → B(5k+10) |

B(n) is state B reading the first blank to the right of a contiguous block of n ones, with zero rays elsewhere. X(a,b) is state C with outward rays 01^a and 01^b; Y(a,b) replaces the right ray by 1^b. All rays have zero extension.

The exact primitive rules are B(a+2) → X(a+1,1) (8 moves), X(a+2,b) → X(a+1,b+1) (7), X(1,b+2) → Y(5,b) (11), and Y(a,b+5) → Y(a+5,b) (9/11/17 depending on C1). For codes 13/15 the first rightward sweep lands at Y(a,0)=X(a,0), and a second left/right sweep lands at Y(a,2), from which B(a+3) is reached in 6/8 moves. For code 19 a single pair of sweeps reaches Y(a,2), followed by B(a+5) in 16 moves. Induction over the two sweeps gives the displayed uniform growth; a second induction gives arbitrarily long successful runs from the literal blank configuration, so F0 is never queried in this ray model.

[UnaryGrow.lean](UnaryGrow.lean) was compiled locally with Lean 4.36.0-rc2. The exported growR, growE, never depend only on propext and Quot.sound. [UnaryGrowBridge.lean](UnaryGrowBridge.lean) binds literal transition tables and transports every successful run to the original physical machine. Both modules compiled locally against the original accepted dependency modules from artifact 15175093456; the source bridge's `table_match`, `observe_move`, and `never` use only propext and Quot.sound, and `weighted` additionally uses Classical.choice. This establishes the three literal local Covers at every bound, with no sorryAx. It does not establish the parent Cover or a global roster cut.

The remaining 898 additional leaves have untrusted side-cycle or block-FAR candidate recipes (some reflected, requiring an appropriate reflection-aware emitter). The recipes are stored in `recipes-d0le.json`; the reflected transfer theorem in `UnaryGrowReflect.lean` compiled against the same original modules. Source acceptance of the block leaves and the complete parent composition remain open.
