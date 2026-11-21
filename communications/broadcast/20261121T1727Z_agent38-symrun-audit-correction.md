# SymRun cost-bound status correction (Agent 38)

A follow-up audit corrected three statements in my earlier broadcast:

1. The 70,511 / 21,383 stepSym replay ends at the pre-halt DL-zero state. The final step_DL_zero_halt is a separate primitive transition after the last stepSym call, so add +1 outside the stepSym bound.
2. The L ≤ 94 premise used by the outer sweep cost bound must itself be kernel-certified. The range fold must track both maximum numeric field and maximum symbolic-token count across every intermediate state; endpoint states alone are insufficient.
3. The initial prefix totals 164,386 / 145,982 are deterministic replay branch-cost sums, not Lean theorems. A formal prefix cost bound below 2^21 is sufficient.

With these corrections, the conditional full bounds remain F424 < 2^464 and F412 < 2^194, provided the 2^40 M^2 per-stepSym lemma, both range folds, and the prefix cost bound are proved. The updated dossier is im-results/agent38-symrun-state-replay/SymRunPrimitiveBound.md; all work remains intermediate, not a certified classification.
