# SymRun symbolic field-growth bound

The exact repository proof is now appended to
`im-results/agent42-cryptids-upstream-191-overlap/SymRunTraceStats.lean`:

- `stepPure_field_growth`: every `stepPure` transition increases the maximum
  numeric run/repeat field across the two symbolic stacks by at most one.
- `stepPureIter_field_growth`: after `n` pure symbolic transitions, the
  maximum field is at most its initial value plus `n`.

The proof decomposes the BB, DL, and CB branches. The main reusable
ingredients are:

1. `bumpSymL/R` increase the list maximum by at most one;
2. `prependZeroSym` preserves the maximum;
3. `peelPureTok` does not increase the maximum;
4. successful `stripPrefixSym` matches leave a suffix whose maximum is
   bounded by the original list maximum;
5. the CB repeat-token branches that increment a repeat counter are charged
   against the same counter already present on the opposite stack.

## Local preflight and scope

A standalone Lean 4.36.0-rc2 scratch module compiled with the relevant
`SymRunEngine` definitions copied from the pinned upstream source
`google-deepmind/cryptids` commit
`3647718b5df22e1a61462dec0376bd204526285a`. Its
`#print axioms stepPure_field_growth` and
`#print axioms stepPureIter_field_growth` profiles are both
`[propext, Quot.sound]`.

This is a source-equivalent proof-fragment preflight, not yet compilation of
the exact imported `SymRunTraceStats.lean` closure. Exact-source compilation
and axiom audit remain required before acceptance. The theorem is for
`stepPure`; it does not by itself establish a bound for `stepSym` or a
complete machine-run bound.


## CB sweep token bound (independent check of 564/570)

The same proof harness now also proves the following source-level inequalities:

- `sweepCB_length_bound`:
  `|sweepCB(L,R)| ≤ |L| + |R| + 5|R| = |L| + 6|R|`.
  The proof uses strong induction on `|R|`; every recursive sweep call
  consumes at least one right token. Each run-triggered call adds at most
  five tokens via `bumpSymL`; each repeat-eating call adds at most one
  token via `eatFuel`, while consuming the right-side repeat token.
- `sweepCB_length_le_564`: if the input total token count is at most 94,
  the CB sweep output has at most 564 tokens.
- `stepElemCB_BB_length_bound`: whenever `stepElemCB` returns mode BB,
  its output has at most the input total plus six tokens.
- `stepElemCB_after_sweep_570`: if the CB-sweep input has at most 94 tokens
  and the subsequent `stepElemCB` fallback returns BB, the state passed to
  the ensuing BB sweep has at most 570 tokens.

These are conditional bounds. The 94-token premise must be supplied by the
appropriate trace invariant (the existing `traceStats` theorems establish it
for their named candidate traces); the 570 theorem also requires the BB
fallback premise. The local Lean 4.36.0-rc2 scratch compilation reports only
`[propext, Quot.sound]` for the three principal bounds. Exact compilation
against the repository's imported module closure is still pending.


## Additional costed CB atomic witnesses

I also added two candidate exact-time reachability witnesses to
`im-results/agent42-cryptids-upstream-191-overlap/SymRunCostedStepPilot.lean`:

- `step_CB_run0_nil_exact`: C-zero/nil to BB in 3 primitive steps;
- `step_CB_run0_zero_exact`: C-zero/zero to BB in 5 primitive steps.

Agent 42 checked these against the exact pinned F424 module and corrected the
initial candidate costs: C-zero/zero is 3 (not 5), and generic B-succ is 3
for every right stack (so the zero-headed specialization is 3, not 4).
The current pilot source at main commit `878cea49725c3392e4107ab314829a02b508086f`
contains the corrected counts. They use `executeWithin` and `ReachesIn`;
exact module compilation remains pending.


Two additional candidate costed BB witnesses are now in the pilot:

- `step_BB_run1_nil_exact`: B-succ followed by BR-nil, 3 primitive steps;
- `step_BB_run1_zero_exact`: B-succ with zero-headed right stack, 3 primitive steps.

Agent 42's exact-source review corrected the zero-headed specialization to
3 steps as well; the generic B-succ rule is 3 for every right stack. The
current pilot at main commit `878cea49725c3392e4107ab314829a02b508086f`
contains the corrected counts. Exact module compilation remains pending.
