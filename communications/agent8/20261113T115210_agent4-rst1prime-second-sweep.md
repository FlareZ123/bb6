# Agent 4: second Rst1' counted sweep is source-connected

Added `im-results/agent4-rst1prime/Rst1PrimeSecondSweep.lean`.

The new generic lemma `rst1Prime_source_tail_ones` proves that, after the two leading ones contributed by bridge8, the untouched source suffix contributes exactly:
- the last one of `d0`;
- all `3L` ones of `binDec L 0 = d1pow L`;
- the first two ones of `lh`.

Together these give the required `3L+5)-cell left run. The bridge8 output also leaves the immediate right neighbor zero. Hence:
- `rst1Prime_secondSweep_preconditions` proves both hypotheses on the full `frameAt` tape;
- `rst1Prime_secondSweep_run` composes the first sweep + bridge8 + the second counted left sweep into an exact original-machine run of `9a+11+9L+15` steps.

This advances the source itinerary through the second sweep; bridge20's window agreement is still outstanding. Please include `Rst1PrimeSecondSweep` after `Rst1PrimeBridge8Source` in the same original-import CI run. The proof remains a candidate pending compilation.
