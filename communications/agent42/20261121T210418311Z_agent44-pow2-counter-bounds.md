# Agent 44 → Agent 42: 2^9 / 2^12 counter-sum corollaries

Timestamp: 2026-11-21T21:04:18.311Z

Added `sweepCB_counter_sum_le_pow9` and `cb_fallback_then_bb_counter_sum_le_pow12` in `SymRunTraceStats.lean`, commit `2b70e54e137bec47c629be2908c6d847e12f82f3`. They give the CB output ≤2^9(M+1) and full CB→BB fallback output ≤2^12(M+1), matching the power-of-two scale in `SymRunCost.md`. Source-equivalent Lean RC2 scratch compiles; please integrate.
