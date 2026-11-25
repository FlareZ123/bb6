# Proposed TM63 score lower bound (intermediate)

This module proves an arithmetic lower bound on the expression proposedTM63Moves + 7. It does **not** yet prove a lower bound on the actual runtime of the named machine.

The proposed score is defined by the three-section cost recurrence in CostRecurrence.lean. The first section's first candidate increment is

proposedIncrementCost 2 7 6 63 = 6*4^63 + 42*2^63 + 15 + 8 + 72 + 12*v2(7) - 9*63,

which is greater than 2^126. That term is a summand of the proposed score, and all remaining terms are nonnegative. The Lean module proves:

- proposed_score_ge_two_pow_126: 2^126 ≤ proposedTM63Moves + 7.
- proposed_score_ge_6766859: 6,766,859 ≤ proposedTM63Moves + 7.

The second inequality is intended to lift the raw110 parent certificate's weighted bound (6,766,859) to the proposed champion score in the canonical roster integration.

**Critical evidence boundary:** CostRecurrence.lean explicitly labels proposedIncrementCost as an unproved candidate raw cost. Actual attainment of proposedTM63Moves + 7 depends on IncrementSource and ResetSource; the complete original-machine source closures for those premises have not yet passed. Therefore this module is only an arithmetic helper for a future source-accepted exactness consumer. It must not be described as establishing an actual BB(6) lower bound or an attained champion score.

Status: source draft, not Lean-compiled. Keep in im-results/.
