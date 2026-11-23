# SymRun symbolic-state growth and field potential

This dossier develops source-level bounds for the symbolic-run engine in
`google-deepmind/cryptids` commit
`3647718b5df22e1a61462dec0376bd204526285a`.

## Current strongest BB-sweep argument

The current BB-sweep route separates output token length from numeric-field
mass and combines them only after the two inductions:

- `sweepBB_length_bound4_pair`: simultaneous induction with an ordinary
  right-stack bound and a one-unit stronger bound when the right stack begins
  with run 0.
- `sweepBB_length_bound4`: output token count is at most
  `|L| + |R| + 4*|L| + 12`.
- `sweepBB_num_sum_bound`: output numeric-field sum is at most
  `numSum(L) + numSum(R) + 2*|L| + 5`.
- `sweepBB_weight_bound_sharper`: with
  `symStateWeight = tokenCount + numericFieldSum`, the combined estimate is
  `W_out ≤ W_in + 6*|L| + 17`.
- `sweepBB_field_max_le`: output maximum numeric field is at most
  `numSum(L) + numSum(R) + 2*|L| + 5`.

Here the corresponding augmented input potential is
`W_in = 1 + |L| + |R| + numSum(L) + numSum(R)`, and the output potential
adds the leading 1 to `symStateWeight). Algebraically, the draft estimate
implies `W_out ≤ 7*W_in + 11 ≤ 9*(W_in + 1)` for `W_in ≥ 1`.
This is a source-generic BB-sweep lemma, not yet a bound on the full
`stepSym` transition or on blank-root primitive runtime.

The key amortized invariant is the leading-run0 shield. In the ordinary
induction case, a run-1 head can incur the generic five-token bump expansion,
but the recursive right stack is prefixed by run 0 and therefore admits the
stronger bound. In the shielded case, bumping a right stack already beginning
with run 0 changes its head to run 1 without increasing its length. Successful
B2/B12R eats preserve the shield; B1 eats may lose it but shorten the right
stack enough to use the ordinary bound.

## Exact-source module split

The earlier broad workfile
`../agent42-cryptids-upstream-191-overlap/SymRunTraceStats.lean` is not a
valid exact-source dependency as a whole. The pinned RC2 run
[45137136319](https://github.com/FlareZ123/bb6/actions/runs/45137136319)
reported independent errors outside the BB-sweep helper closure, including:

- theorem proof constants incorrectly used as propositions in the
  F424/F412 range aggregates and checkpoint certificates;
- unresolved field-growth and `stepPure` proof goals;
- unresolved branches in `stepElemCB_BB_length_bound`.

The BB-specific helper declarations near the end of that file did compile
without `sorryAx`, but the module-wide errors prevented acceptance of any
downstream certificate. Rather than silently treating those declarations as
accepted or repairing unrelated code merely to unblock this result, the
needed helper closure was extracted to
`SymRunBBBase.lean`. It contains the exact-source BB length, numeric-mass,
and field-maximum lemmas, without the unrelated legacy declarations.

`SymRunBBBounds.lean` now imports `SymRunBBBase`; the theorem
`sweepBB_weight_bound_sharper` is placed after
`sweepBB_num_sum_bound` to avoid a forward reference.
`SymRunTraceStatsAudit.lean` imports the isolated base and BB bounds and
prints the transitive axiom profiles of the resulting lemmas.

## Status and acceptance boundary

**The BB-sweep bounds remain unaccepted drafts.** The exact-source audit
[45145550915](https://github.com/FlareZ123/bb6/actions/runs/45145550915)
is the current focused run, pinned to the Cryptids commit above and Lean
`v4.36.0-rc2`, with dependency chain:

`SymRunBBBase.lean → SymRunBBBounds.lean → SymRunTraceStatsAudit.lean`.

The preceding runs [45144046165](https://github.com/FlareZ123/bb6/actions/runs/45144046165)
and [45144654362](https://github.com/FlareZ123/bb6/actions/runs/45144654362)
were cancelled before the proof stage after static dependency review found
successive omissions in the isolated field-maximum closure. The current base
now includes the field-max definitions, append/cons lemmas, and the
numeric-sum bridge; neither cancelled run provides proof evidence.

The earlier exact-source runs
[45129145926](https://github.com/FlareZ123/bb6/actions/runs/45129145926) and
[45132510153](https://github.com/FlareZ123/bb6/actions/runs/45132510153)
also failed. The local source-equivalent Lean harnesses used for earlier
field-growth, CB-length, counter-sum, and numeric-sum experiments are useful
development evidence only; they do not replace the pinned source audit.

The intended acceptance standard is kernel-checked compilation of the
complete dependency closure and exported transitive axiom profiles without
`sorryAx` or `native_decide`. Standard Lean axioms such as `propext`,
`Quot.sound`, and where justified `Classical.choice` are not equivalent to
admitting an unproved theorem.

## Remaining route to a full source-cost bound

1. Complete the focused BB-sweep exact-source audit and repair only concrete
   compiler failures.
2. Isolate and repair the CB-sweep and BB-producing fallback length/mass
   lemmas. The current broad Stats module's
   `stepElemCB_BB_length_bound` has unresolved branches and its F424/F412
   trace aggregates are not yet valid certificates.
3. Coordinate the accepted BB/CB exports with Agent 42's independent
   `stepSym` wrapper composition.
4. Compose the complete macro-cost inequality with source-native primitive
   cost envelopes and exact blank-root checkpoint chains.
5. Keep every candidate primitive-time classification conditional until
   the original-machine one-step and macro-dispatch bridges are
   kernel-checked.

No claim here establishes a universal six-state upper bound or determines
BB(6).
