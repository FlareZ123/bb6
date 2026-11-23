# SymRun symbolic-state growth and field potential

This dossier develops source-level bounds for the symbolic-run engine in
`google-deepmind/cryptids` commit
`3647718b5df22e1a61462dec0376bd204526285a`. The main formal source is
`../agent42-cryptids-upstream-191-overlap/SymRunTraceStats.lean`.

## Current strongest bounds

### Pure-step field growth

The source-equivalent proof harness establishes:

- `stepPure_field_growth`: one `stepPure` transition raises the maximum
  numeric run/repeat field by at most one.
- `stepPureIter_field_growth`: after `n` pure transitions, the maximum
  field is at most its initial value plus `n`.

The proof uses the exact BB, DL, and CB cases, with reusable bounds for
`bumpSymL/R`, `prependZeroSym`, `peelPureTok`, and prefix stripping.
This is a theorem about `stepPure`, not the outer `stepSym` transition.

### CB token and field bounds

The imported-source file contains the following source-generic lemmas:

- `sweepCB_length_bound`: output token count is at most
  `|L| + 6*|R|`.
- `sweepCB_length_le_564`: with at most 94 input tokens, the CB sweep
  outputs at most 564 tokens.
- `stepElemCB_BB_length_bound`: a BB-producing elementary CB step adds at
  most six tokens.
- `stepElemCB_after_sweep_570`: the subsequent BB-sweep input has at most
  570 tokens, under the explicit 94-token and BB-branch premises.
- `sweepCB_counter_sum_bound`: repeat-counter sum grows by at most
  `4*|R|`; with 94 input tokens this gives `94*M + 376`.
- `cb_fallback_then_bb_counter_sum_94M2656`: the complete CB-sweep,
  BB-producing fallback, and BB-sweep path has repeat-counter sum at most
  `94*M_CB + 2656`.
- `sweepCB_num_sum_bound`: numeric-field sum grows by at most
  `3*|R|`; with 94 input tokens it is at most `94*M_CB + 282`.
- `cb_fallback_bb_input_field_max_le_94M285`: the field maximum at the
  BB-sweep input is at most `94*M_CB + 285`, hence at most
  `2^9*(M_CB+1)`.

The 94-token premise is established by the finite `traceStats` certificates
for the named F424 and F412 source traces. The fallback results also require
the stated BB-output branch condition.

### BB-sweep combined potential — formal draft

The latest addition to `SymRunTraceStats.lean` is:

```lean
symStateWeight (sweepBB L R) ≤
  L.length + R.length + listNumSum L + listNumSum R
    + 8 * L.length + 18
```

Here `symStateWeight` is total symbolic token count plus numeric-field
sum; adding one gives the coarse potential
`W = 1 + |L| + |R| + numSum(L) + numSum(R)`.

The proof draft adds:

- numeric-sum and length bounds for `eatB2` and `eatB12R`;
- a length bound for `peelTok`;
- a total-token bound for `stepElemBB`;
- a strong induction over the exact `sweepBB` cases.

Successful repeat-eat branches transfer the consumed left repeat field to
the returned right suffix. The run-1 recursive branch is covered by the
eight-unit per-left-token allowance. Failed repeat matches are terminal and
are covered by the fixed additive allowance.

**Status:** committed in `SymRunTraceStats.lean` at
`fbaac854103fd5cad922e473140ca5d2cd420ad0`, but not yet accepted as a
formal result. Exact-source Lean 4.36.0-rc2 audit run
[45129145926](https://github.com/FlareZ123/bb6/actions/runs/45129145926)
is in progress. The audit compiles the pinned F424 and F412 modules, then
the complete `SymRunTraceStats.lean` file and
`SymRunTraceStatsAudit.lean`. Until that run succeeds, treat the new BB
potential theorem as a proof draft.

If accepted, the theorem gives
`W(sweepBB(L,R)) ≤ W(BB,L,R) + 8*|L| + 18`, and hence the coarse
multiplicative estimate `W_out ≤ 27*(W_in+1)`. This is one component of
the global `stepSym` potential argument, not yet a complete primitive-time
bound.

## Exact-source and acceptance boundary

The local source-equivalent Lean 4.36.0-rc2 harnesses used for the earlier
field-growth, CB-length, counter-sum, and numeric-sum results are useful
development checks, but do not substitute for compiling the exact imported
source closure. The previous shared exact-source audit
[44955198218](https://github.com/FlareZ123/bb6/actions/runs/44955198218)
failed after the statistics module emitted its axiom reports. The current
audit run above isolates the statistics module and its axiom bridge.

The proof is intended to remain kernel-checked without `sorryAx` or
`native_decide`. Existing `#print axioms` reports for the older lemmas
include standard Lean axioms such as `propext`, `Quot.sound`, and in some
CB results `Classical.choice`; these are distinct from admitting an
unproved theorem.

## Next formal steps

1. Resolve the current exact-source audit, repairing only concrete compiler
   failures.
2. Use the BB-sweep weight bound with the existing CB/DL branch bounds to
   prove a global `stepSym` potential inequality.
3. Compose that inequality with the already-developed source-native
   primitive-cost envelopes and exact F424/F412 checkpoint chains.
4. Keep all resulting candidate primitive-time classifications conditional
   until the original-machine one-step and macro-dispatch bridges are
   kernel-checked.
