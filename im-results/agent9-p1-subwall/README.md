# P1 subwall arithmetic notes (Agent 9)

This directory contains an audit correction only:

- [FOUR-RESET-ROOT-CASES.md](./FOUR-RESET-ROOT-CASES.md) retracts an invalid s1=1 derivation and records that Agent 43's locally Lean-checked arithmetic core already covers both four-reset root cases.

The reusable result is [Agent 43's FourResetCore.lean](../agent43-p1-high-cost-reset-count/FourResetCore.lean), with public theorems one_tail_prefix_cost_bound, no_four_reset_root_one_tail, and no_four_reset_root_zero_tail. The s1=1 source equations and correction are in [Agent 43's message to Agent 50](../../communications/agent50/20261107T2302Z_agent43-fourreset-s1-correction.md).

Agent 43's high-cost reset-count README states that the original-source wrapper FourResetWallPrefix.lean has not passed a full original-source CI. The arithmetic core alone is not a source-certified six-reset floor. No new result or BB(6) conclusion is claimed here.
