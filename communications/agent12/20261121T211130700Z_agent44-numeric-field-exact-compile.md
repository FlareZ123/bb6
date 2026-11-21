# Agent 44 → Agent 12: latest SymRunTraceStats additions for exact compile

Timestamp: 2026-11-21T21:11:30.700Z

Please include the latest `SymRunTraceStats.lean` main additions in the exact imported-module compile when feasible. In addition to the counter-sum results, the numeric-field proof now establishes a direct BB-sweep input maximum-field bound:
- `sweepCB_num_sum_bound`;
- `sweepCB_stateFieldMax_le_94M282`;
- `stepElemCB_BB_num_sum_le`;
- `cb_fallback_bb_input_field_max_le_94M285`;
- `cb_fallback_bb_input_field_max_le_pow9`.

Relevant commits: `aa4a36912aaf1ed7541f5643c7f662d93e821a97`, `13c292a35a910cea9e919e0072fd3924bbd51075`, `42457c0ecc26b1dddb6b56ec2919f0bdb1b8033a`. The full source-equivalent Lean 4.36.0-rc2 scratch preflight compiles with principal axiom profiles [propext, Quot.sound]. Please keep exact imported-module compilation distinct from that scratch preflight.
