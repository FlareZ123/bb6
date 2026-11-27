# Raw36 corrected holdout transfer

Input: Agent29 corrected recovery artifact 15234603701, 366 unresolved literal tables after 27 of 393 OPEN tables were recovered using the <=4-state FAR bank.

All 366 have exact nonhalting certificate candidates: 350 FAR and 16 inductive sweep proofs. All 350 FAR fixed points were reconstructed independently with arbitrary precision; 120 literal FAR theorems (shards 00–05) have been locally Lean-checked against the accepted Raw36 source closure. All 16 sweep theorems were locally Lean-checked against the original SweepPumping module from artifact 15233523548, with only propext and Quot.sound. Full corrected parent-tree generation and source CI acceptance remain outstanding.

The compressed exact table-keyed fixture and emit.py reconstruct FAR.Data witnesses without dependence on tree ordinals. Starting from 261 Raw49 automata, direct transfer covered 81, single-transition mutations 223 total, repeated winner mutations 339, state splitting and follow-up mutations 348, and one 11-state witness covered the final two FAR tables. There are 78 distinct winners. The fixture uses base36 digits for DFA targets (a=10).

sweep_recipes.jsonl stores the 16 remaining literal tables, their reachable base configurations and symbolic opaque-tail sweep/finite-step recipes. Generate:

    python im-results/agent7-raw49/emit_sweep_recipes.py im-results/agent7-raw36-transfer/sweep_recipes.jsonl BB6.Agent7Raw36Sweeps Raw36TransferSweeps.lean

Each M<id>.never theorem proves nonhalting of every compatible total machine. M340 reaches state E with left tape 0111 at step 117 and grows a repeated 30-bit right word with epoch cost 504*n+824.

The 350 FAR keys and 16 sweep keys cover the archived 366; include the separate 27 original recoveries when rebuilding the corrected 393-OPEN subtree. Retain the corrected score cutoff (including Agent29's 1016-step halter, weighted 1022). This is a leaf-certificate result, not a parent Cover or global roster reduction.
