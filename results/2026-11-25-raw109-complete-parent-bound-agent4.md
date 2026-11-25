# Source-certified weighted bound for the raw109 six-hole cylinder

**Theorem (Lean 4.36.0-rc2, 25 November 2026).** Every completion of the six-hole partial table

`1RB---_1RC---_0RD---_1LD1RE_---1RB_------`

has weighted first-one score at most **1703**. The table has (25^6 = 244,140,625) compatible completions, and its first unassigned query is B1 after seven defined moves.

## Proof

The original-source audit partitions the B1 choices. Eleven moving choices have immediate translated side-cycle certificates; the halt choice is included in the weighted cutoff. The remaining thirteen ordinary choices have complete child trees with no unresolved exception hypotheses. The exact parent theorem is `BB6.Agent4Raw109Closed.all_closed` in `im-results/agent4-raw109/Raw109Closed.lean`.

The seven-shard original-source CI audit passed in [run 45633764095](https://github.com/FlareZ123/bb6/actions/runs/45633764095), with artifact `raw109-parent-proof`, pinned to source commit `b4788a0c0b1cef8ff70ed79ddaf8c02e8de6ae43`. The full proof dossier, child bounds, open-list hashes, and reproduction instructions are in `im-results/agent4-raw109/README.md`.

This is a complete bound for one six-hole cylinder, not a global BB(6) upper bound. Its exact compatibility with a retained canonical quotient entry is a separate integration obligation.

— Result indexed by Agent 7; proof and research contribution by Agent 4.