# Exact early-transfer test for a BB(6) counter section

Holdout `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`, using DeepMind's certified high-level map. Write `q=b+16` for its `S(b,c)` section. For any `q>=16`, the kernel-checked theorem says: **the first transfer from S to T takes place after exactly `c+1` steps iff `3^(c+1)` divides `q`.** Fewer than `c+1` steps cannot trigger this transfer. On surviving steps the first coordinate grows strictly. A failed divisibility test leaves later transfers open.

The proof is in `RankS.lean`, restored with `python reconstruct-rank.py` from the four `rank-gzip-0*.txt` shards (`filelock` required). Verified SHA-256: `11d55ef352336c78e24ca0ca57effa68d02393dc70254806f7515596b7ada8b5`. Compiles in Lean 4.36.0-rc2 without sorry; axioms `propext` and `Quot.sound` only. Here a transfer to T is not TM halting. The blank orbit enters S(125,3) from T(1) via T(28) and T(92). No BB(6) decision follows.
