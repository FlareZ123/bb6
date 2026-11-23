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

### BB-sweep amortized potential — formal drafts

An initial direct combined-potential proof in SymRunTraceStats.lean was
withdrawn after the first exact-source CI run exposed arithmetic and
unsolved-goal errors. Rather than patching a weaker one-pass induction, the
current route separates token length from numeric mass in the dedicated
`SymRunBBBounds.lean` module below. The simpler direct proof is no longer
claimed or retained.

A sharper independent derivation is drafted in
`SymRunBBBounds.lean`. It separates token length from numeric mass:

- `sweepBB_length_bound4_pair`: simultaneous induction with an ordinary
  right-stack bound and a one-unit stronger bound when the right stack begins
  with run 0.
- `sweepBB_length_bound4`: output token count is at most
  `|L| + |R| + 4*|L| + 12`.
- `sweepBB_num_sum_bound`: output numeric-field sum is at most
  `numSum(L) + numSum(R) + 2*|L| + 5`.
- `sweepBB_weight_bound_sharper`: combining the two gives
  `W_out ≤ W_in + 6*|L| + 17`.
- `sweepBB_field_max_le`: output maximum numeric field is at most
  `numSum(L) + numSum(R) + 2*|L| + 5`.

The key amortized invariant is the leading-run0 shield. In the ordinary
induction case, a run-1 head can incur the generic five-token bump expansion,
but the recursive right stack is prefixed by run 0 and therefore admits the
stronger bound. In the shielded case, bumping a right stack already beginning
with run 0 changes its head to run 1 without increasing its length. Successful
B2/B12R eats preserve the shield; B1 eats may lose it but shorten the right
stack enough to use the ordinary bound.

If accepted, the sharper estimate gives
`W_out ≤ W_in + 6*|L| + 17 ≤ 24*(W_in+1)` for `W_in ≥ 1`.
This is sufficient to retain the coarse multiplicative factor used in the
CB fallback analysis. The field-maximum corollary also gives a direct
source-generic bound for the state after a BB sweep.

**Status:** both derivations remain drafts. The first exact-source run
[45129145926](https://github.com/FlareZ123/bb6/actions/runs/45129145926)
failed on the withdrawn direct combined proof and one missing arithmetic
closure in the atomic length lemma. The failed proof was removed and the
atomic case corrected. A second pinned run is now required to compile
SymRunTraceStats.lean, SymRunBBBounds.lean as an extra dependency, and the
updated axiom bridge. Do not treat the new amortized theorems as formally
accepted before that run succeeds.

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
