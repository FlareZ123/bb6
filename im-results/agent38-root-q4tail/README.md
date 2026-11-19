# Authentic root to q4Tail continuation

`TM63RootQ4Tail.lean` composes two existing exact-run source drafts:

1. Agent 48's `tm63_blank_reaches_second_q4_frame`, which reaches the
   first-cycle endpoint at the authentic blank-root head;
2. Agent 24's `positiveZFirstCycle_then_secondCyclePrefix`, which runs
   from the canonical first q4 checkpoint through the first cycle and the
   second-cycle prefix to `q4Tail`.

The key reduction is deterministic suffix extraction. Agent 24's full
`C1+C2` run and the existing `C1` first-cycle run have the same canonical
start and exact `V) endpoint. By `run_append`, this uniquely determines
the remaining `C2) run from `V). The suffix is then transported to the
authentic root coordinates using `shift_run`. No private tape guards from
Agent 24's theorem are repeated.

The only new arithmetic precondition is that the root P1 counter is odd.
For `A=rootMarker1A=exponent+right+2 ≥ 2`,
`firstQ4P1Value = 2^(A-1)*(2^(L+2)-1)-1` is odd. The existing
`firstQ4P1Value_lt` theorem supplies the BinDec capacity bound, and
`rootMarker1Z_ge_three` supplies the positive-z precondition.

## Status

**Intermediate Lean source draft; not compiled.** Local shell/Python
execution is unavailable in this invocation (tool-level ClientError), and
no CI run has been dispatched. The theorem is only a composition of
existing source-level run statements; it does not prove that the TM63
trajectory halts, does not determine its final score, and does not provide
a BB(6) upper bound.

Next acceptance step: compile the exact import closure under Lean
4.36.0-rc2, inspect the first diagnostics, and run the declared axiom
audit. Keep this in `im-results/` until that acceptance succeeds.
