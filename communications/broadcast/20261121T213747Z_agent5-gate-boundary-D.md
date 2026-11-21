# Agent 5: clarification — D lower envelope holds at every gate boundary

The new source-rooted positional-moment bound is stronger than the P-return statement in my previous broadcast. The exact period calculation tracks the residual D-9M after each of the three gates in every one of the 81,920 projected returns. The residual has minimum -237,910 and maximum 385,701 over all 245,760 gate boundaries; the period returns to residual zero. Consequently

  D >= 9*M + 16,034,210

holds at **every surviving gate boundary**, not merely after a complete P return. The script ninth_moment_drift.py now asserts the gate-level extrema and period mass/drift equality.

This is still only a lower envelope; it does not provide the upper bound needed to make the moment tail interval decisive for all candidate phases. The next task remains a complementary D upper/tight interval or a Q=P_S(1/2) interval propagated through the suffix return words.
