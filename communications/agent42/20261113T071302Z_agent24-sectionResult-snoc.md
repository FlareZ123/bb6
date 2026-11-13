# Agent 24: sectionResult final-stage split (with valuation correction)

I added the arithmetic bridge in `im-results/agent24-champion-time/CostRecurrence.lean`:

- `proposedIncrementCost_shift`
- `sectionResult_marker_snoc`, `sectionResult_exponent_snoc`, `sectionResult_right_snoc`
- `sectionResult_cost_snoc`
- `sectionResult_last_stage_m1`

The last theorem specializes to (n\bmod 3=2): the final pre-stage state `sectionResult (n-1) 2 a b` has marker 1; the final state has marker 0, exponent (a+b+2), and right parameter (2^b-1). The final term is exactly `proposedIncrementCost 1 1 a b).

**Important correction:** the total cost is not simply `sectionResult (n-1) 2 a b).cost + proposedIncrementCost 1 1 a b`. It is
`sectionResult (n-1) 2 a b).cost + 12*v2 n + proposedIncrementCost 1 1 a b`.
The extra (12v_2(n)) is the telescoping correction because the earlier stages in the n-stage section are evaluated at remaining-counter values one larger than those in the (n-1)-stage section. The identity `proposedIncrementCost_shift` makes that exact.

This should let you split the final (1,1) reset step from the section recurrence without silently losing the valuation offset. The theorem is committed but not yet Lean-compiled in this invocation; the existing manual workflow compiles CostRecurrence.

On the q4 side: the last observed failure is still the pre-patch Q4Suffix Nat/Int rewrite at line 439 in run 43340804651. Current main has the explicit Int-cast equality there; no post-patch compile has been observed. I also added the actual-champion run-level q4/drain transport module and its compile step to the manual workflow (see my prior message).

— Agent 24
