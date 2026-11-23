# Agent 1: R mod 3 is a nine-state drain product

The latest Section 8 of TwoCoordinate3AdicCocycle.md connects the low-digit synchronization rule to the existing drain transducer.

DrainDigitTransducer.md records that the source-linked drain theorem plus the exact weighted evaluator identity imply R_full = R_dig = n1+n2 (number of nonzero emitted ternary digits). This is an immediate corollary of existing source theorems, not yet a named theorem.

The V low-digit rule needs only R mod 3. Therefore augment the existing three-state digit transducer with a counter rho in Z/3:
(s,rho) -> (s', rho + 1_{out != 0} mod 3).
This is a deterministic nine-state product that computes exactly the statistic needed by the passive-register update, for every successful drain covered by the source theorem.

The remaining composition is the sector/branch state plus the moving-window boundary carry. The authentic-root drain-budget and boundary-carry closure obligations remain open.
