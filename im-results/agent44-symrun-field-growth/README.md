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


The BB-succ pilot now also contains the stronger generic theorem
`step_BB_run1_exact`, proving the three-step transition for every right
stack `R` to `run0 :: bumpM R`; the nil and zero specializations remain
as simple endpoint smoke checks.


## Formal CB repeat-counter sum bound

The latest source-equivalent Lean preflight also proves a repeat-counter
accounting invariant:

- `bumpSymL/R_counter_sum_le`: bump operations do not increase the sum of
  numeric repeat counters.
- `eatFuel_counter_sum_le`: one eat operation increases that sum by at most
  its fuel (four for each CB repeat-token branch). Existing repeat counters
  are transferred; only matched literal blocks add units.
- `sweepCB_counter_sum_bound`: after the CB sweep, total repeat-counter sum
  is at most the input sum plus `4 * |R|`.
- `listCounterSum_le_length_mul_fieldMax`: a list's counter sum is at most
  its length times its maximum field.
- `sweepCB_counter_sum_le_94M376`: if the input total token count is at
  most 94 and its maximum field is M, the output counter sum is at most
  `94*M + 376`.

This formally supports the counter-sum term used in the source-level
primitive-time estimate. The theorem is conditional on the 94-token premise
and is not itself a complete `stepSym` cost theorem. The new lemmas are in
`SymRunTraceStats.lean` commit `5ef4ccefa8b534ab17af8b95b769bd2894574529`;
the source-equivalent Lean 4.36.0-rc2 scratch axiom profile is
`[propext, Quot.sound]`. Exact imported-module compilation is still pending.


## Formal BB sweep counter-sum bound and CB→BB composition

The same counter-sum accounting has now been carried through the BB sweep:

- `stepElemBB_counter_sum_le`: the BB elementary step does not increase
  repeat-counter sum.
- `peelTok_counter_sum_le`: peeling a repeat token does not increase the
  counter sum.
- `sweepBB_counter_sum_bound`: BB sweep output counter sum is at most input
  counter sum plus `4 * |L|`.
- `sweepBB_counter_sum_le_570M2280`: for a BB-sweep input with at most 570
  tokens and maximum field M, output counter sum is at most `570*M + 2280`.
- `cb_fallback_then_bb_counter_sum`: composes the 94-token CB sweep,
  BB-producing elementary fallback, and 570-token BB sweep bounds. Under the
  explicit 94-token and BB-branch premises, the post-BB-sweep counter sum is
  at most `570*M_BB + 2280`, where M_BB is the field maximum at the BB-sweep
  input.

These results formalize the repeat-counter accounting across the full
CB-to-BB fallback path. They remain conditional on the stated token and branch
premises; they do not yet prove the global `stepSym` primitive-time theorem.
The Lean source is in `SymRunTraceStats.lean`, commits
`52c13f58bbff5e2664c98277f4ee233796dcc6a1` and
`bfd0796912ef25c0cc84b54671dd5d3e7942eb0e`. Source-equivalent Lean 4.36.0-rc2
scratch compilation passes with principal axiom profiles
`[propext, Quot.sound]`; exact imported-module compilation remains pending.


A sharper composition now avoids introducing the BB-sweep input's own maximum
field. The theorem `stepElemCB_BB_counter_sum_le` proves that a BB-producing
elementary CB fallback does not increase repeat-counter sum. Consequently
`cb_fallback_then_bb_counter_sum_94M2656` bounds the counter sum after the
entire CB-sweep → BB-fallback → BB-sweep path by
`94*M_CB + 2656`, where M_CB is the original CB input's maximum field.
The hypotheses remain explicit: input token count ≤94 and the elementary
fallback must return BB. This is stronger than the earlier
`570*M_BB + 2280` formulation because it is expressed using the original
state's M. Added in `SymRunTraceStats.lean` commit
`2dc5bbb67218f5d31a4ce491c916eb846de4fb00`; source-equivalent Lean RC2
scratch compiles with principal axiom profiles `[propext, Quot.sound]`.


For direct use in the coarse power-of-two budget, two arithmetic corollaries
are also formalized:
- `sweepCB_counter_sum_le_pow9`: CB output counter sum ≤
  `2^9 * (M_CB + 1)`;
- `cb_fallback_then_bb_counter_sum_le_pow12`: the complete CB→BB fallback
  output counter sum ≤ `2^12 * (M_CB + 1)`.

These are immediate consequences of the sharper linear bounds and match the
power-of-two scale used in the primitive-time sketch. Added in
`SymRunTraceStats.lean` commit `2b70e54e137bec47c629be2908c6d847e12f82f3`.


## Numeric-field sum groundwork (not yet propagated through sweeps)

A separate measure `listNumSum` counts all numeric fields, including literal
run lengths as well as repeat counters. The source-equivalent Lean proof now
establishes:
- `bumpSymL/R_num_sum_le`: a bump increases numeric-field sum by at most 3;
- `eatStep_num_sum_le` and `eatFuel_num_sum_le`: a matched-block eat does
  not increase numeric-field sum when the block contains at least one unit
  of run length;
- `eatB1/C2/C12_num_sum_le`: the three CB eat operations do not increase
  numeric-field sum.

This is groundwork for a direct maximum-field bound through CB/BB sweeps,
which would complement the repeat-counter-sum theorems above. No sweep-level
numeric-field-sum theorem is claimed yet. The lemmas are in
`SymRunTraceStats.lean` commit `68e4e1b91678b14d8bea7bfc3a5c75c4a8621757`;
source-equivalent Lean RC2 scratch compilation passes.
