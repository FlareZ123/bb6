# Champion score lower bound (intermediate)

This module derives a source-level lower bound on the attained TM63 champion score without evaluating the complete three-section expression.

The exact score is proposedTM63Moves + 7, with
proposedTM63Moves = threeSectionMoves 27959 3 7 6 63. The first source increment in the first section is
proposedIncrementCost 2 7 6 63 = 6*4^63 + 42*2^63 + 15 + 8 + 72 + 12*v2(7) - 9*63,
which exceeds 2^126. Since the full section and remaining stages add nonnegative costs, the champion score is at least 2^126.

The theorem champion_score_ge_6766859 is a corollary. It is intended to lift the raw110 complete-parent certificate (bound 6,766,859) to the champion score in the canonical70 integration.

**Status:** source draft, not yet Lean-compiled. Keep in im-results/; this is a useful threshold bridge, not a standalone publishable BB(6) result.
