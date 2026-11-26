# Raw57/1LA alternating-counter pair

Two one-hole partial machines have exact blank-root four-phase growth proofs in the literal executable zipper semantics. Original-source `NeverHalts` theorems compile locally under Lean 4.36.0-rc2. This is an intermediate leaf result, not a Raw57 parent Cover.

| Open index | Literal table | Epoch cost from parameter n |
|---|---|---|
| 748 | `1RB1LA_1RC0LF_0RD0LE_1LD1RE_0RF0LA_---1RC` | 360+160n |
| 944 | `1RB1LA_1RC0RD_0RD0LE_1LD1RE_0RF0LA_---1RC` | 292+128n |

In the original Z0 convention, left includes the scanned cell and both lists are nearest-first, blank-padded. Let S(n,R) be state A with empty left list and right word 11(01)^(2n+1)R. Blank reaches S(0,empty) after 9 primitive steps. For both tables a reset and three increments yield the exact epoch:

    S(n,empty) -> S(n,10101) -> S(n+1,101) -> S(n+2,1) -> S(n+3,empty).

The initial scan uses an F-state four-bit alternating block transfer. For nonempty suffix, the fixed 13-step turn creates an A-state left alternating word and right frame 11101. The backward sweep consumes each left pair 01 and adds it just after right frame 111, at 18 or 14 steps. A fixed final return restores the section frame 11 and adds the final pair. The empty-suffix branch has two additional fixed carry macros; together they consume one left pair and synthesize the three-token suffix. All the local transitions hold for arbitrary untouched list tails by definitional reduction. Induction using the existing sweep lemmas establishes the unbounded epoch, not an extrapolation from simulation.

Source: [Raw57Alternating.lean](Raw57Alternating.lean), namespace `BB6Coverage.Agent40Raw57Alternating`. Parameter false is 748 and true is 944. Local Lean 4.36.0-rc2 rebuilt the original five dependency modules from artifact 15057164854 and compiled the exact committed proof (blob 68d935a88dd85ca7fbd6154fb5abb025ac9bfb24) plus both per-row wrappers. The theorem `never` and both wrapper theorems have only [propext, Quot.sound] axioms. Source blobs: Frontier 115438c4f244b5416a91be4dd7a3f12103d5448d; Symmetry 84f62dcea34e7f2a97d07016cc2d9065d4ddd7ce; RootShift 80b56fb040f7db81277fcf52cd43e6127fe365ba; SparseZipper 8081dc82ca1e892ab2f6c698d94b6dc24129f6e6; SweepPumping e518c288ecdf5c96890ad64b5971f5c2f18a2106. The 1LA spec now routes both indices through their `.proven` wrappers; the parent audit remains outstanding. No accepted parent count is claimed.
