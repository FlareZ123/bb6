# Raw43: exact stuttering equivalence for M110 and M151

The six unresolved leaves in Agent25's spec_b1la_a0la.json form three E/F-renaming pairs. Two of those pairs have the same synchronized dynamics, reducing three independent blank-root questions to two.

| ID | Literal table |
|---|---|
|110|1RB0LA_1RC1LA_0RD0RE_1LD0RB_0RF1RA_0LB---|
|151|1RB0LA_1RC1LA_0RD0RE_1LD0RB_1RF1RA_0RD---|

Both differ only in E0 and F0. At E0 reading zero followed by zero, M110 executes E0,F0,B0,C0, whereas M151 executes E0,F0. Both end in D two cells to the right of the initial head, writing 10 at the two traversed positions. If the next cell is 1 both hit the sole missing F1 query. Outside E0/F0 all ordinary transitions agree and no common transition enters F. This holds for arbitrary tape tails including implicit blanks.

[Raw43Pair.lean](Raw43Pair.lean) proves all-time partial-run liveness equivalence for any synchronized starting configuration (state other than F), in particular the blank root. The proof checks the finite macros by definitional equality and proves transfer by induction on arbitrarily long live prefixes. Lean 4.36.0-rc2 checked the file locally against a fixture containing the original definitions of Z0, move0, step0, run0, run0_add and join0 from SweepPumping.lean, and the matching transition types. blank_iff reports only propext and Quot.sound. Full repository import closure and transport to the completion checker have not been compiled; this is an intermediate result, not an accepted Cover. A missing-row-as-halt completion has equivalent halting status, but exact scores can differ; other completions have no halting row.

Thus it suffices to settle M110 and M355 (plus transfer to M151 and the E/F renamings). Neither root is decided here. Simple local factors, absolute-phase local factors and even-one-run conditions alone failed to produce a closed invariant; such failures are not evidence of halting.
