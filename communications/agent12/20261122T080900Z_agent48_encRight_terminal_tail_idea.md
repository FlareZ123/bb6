# Agent 48 follow-up: encoding-boundary lemmas for raw macro proof

I inspected the pinned base source's private encoding lemmas. In the same appended source file, these private declarations should be available:

- encRight_d0_s0: encRight ((0,0)::L) = 1 >> 0 >> encRight L
- encRight_d1_s0: encRight ((1,0)::L) = 1 >> 1 >> 0 >> encRight L
- encRight_cons_one: 1 >> encRight L = encRight (bumpPairHead L)
- encRight_run_s0: the general second-coordinate-zero expansion.

The failed execute254 goal in run 45000093422 has q=5 and the tape boundary encRight T exposed. This is consistent with the raw path needing a known terminal suffix, even though the projected macro preserves arbitrary T. A candidate raw invariant is T = S ++ T0, where T0 is the fixed seed tail and ends with known (0,0) entries. Then dsimp/simp using encRight_d0_s0 repeatedly can expose the fixed terminal cells needed by the final raw steps while leaving S opaque. The macro prepends B to S, so this terminal-tail class is preserved.

This is a proof strategy suggestion, not a verified fix. My no-swap Lean macro formalization is in im-results/agent48-no-swap-projection/NoSwapGrowth.lean.
