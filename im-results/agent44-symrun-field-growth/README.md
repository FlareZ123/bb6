# SymRun symbolic-state growth and field potential

This dossier develops exact-source growth bounds for the symbolic-run engine
in `google-deepmind/cryptids` at commit
`3647718b5df22e1a61462dec0376bd204526285a`. The audited machine modules are
F424 and F412, compiled with Lean `v4.36.0-rc2`.

## Mathematical statements

### BB sweep

The BB-sweep argument separates token length from numeric-field mass and
combines them only after the two inductions:

- `sweepBB_length_bound4_pair`: simultaneous induction with an ordinary
  right-stack bound and a one-unit stronger bound when the right stack begins
  with run 0.
- `sweepBB_length_bound4`: output token count is at most
  `|L| + |R| + 4*|L| + 12`.
- `sweepBB_num_sum_bound`: output numeric-field sum is at most
  `numSum(L) + numSum(R) + 2*|L| + 5`.
- `sweepBB_weight_bound_sharper`: for
  `symStateWeight = tokenCount + numericFieldSum`, the output is bounded by
  `|L| + |R| + numSum(L) + numSum(R) + 6*|L| + 17`.
- `sweepBB_field_max_le`: output maximum numeric field is at most
  `numSum(L) + numSum(R) + 2*|L| + 5`.

With augmented potential
`W = 1 + |L| + |R| + numSum(L) + numSum(R)`, the sharper weight statement
gives `W_out <= 7*W_in + 11 <= 9*(W_in + 1)` for `W_in >= 1`.

### CB sweep followed by the BB-producing fallback

`SymRunCBFallbackAudit.lean` isolates the CB-to-BB numeric-mass proof from
the unrelated trace aggregates and primitive-cost drafts in the broad
`SymRunTraceStats.lean` workfile. It reuses `SymRunBBBase.lean` and
`SymRunBBBounds.lean` and states the following conditional bounds:

- `sweepCB_num_sum_le_94M282`: if `|L|+|R| <= 94`, then after the CB sweep
  the numeric sum is at most `94*M + 282`, where `M` is the input maximum
  numeric field.
- `cb_fallback_bb_input_field_max_le_94M285`: if the next CB element step
  enters BB, its output maximum field is at most `94*M + 285`, hence at most
  `2^9*(M+1)`.
- `stepElemCB_after_sweep_570`: the CB sweep and BB-producing element step
  leave at most 570 symbolic tokens.
- `cb_fallback_then_bb_sweep_field_max_le_2pow11`: under the same 94-token
  premise and BB-branch hypothesis, the subsequent BB sweep has maximum field
  at most `2^11*(M+1)`.
- `cb_fallback_then_bb_sweep_weight_le_2pow13`: under the same hypotheses,
  the augmented symbolic-state weight after the subsequent BB sweep is at
  most `2^13*(M+1)`.

These are conditional symbolic-state inequalities. They do not by themselves
establish the 94-token invariant for a blank-start trace, prove the complete
`stepSym` dispatcher, or classify F424/F412 primitive runtime.

## Exact-source modules and CI evidence

The intended dependency chain is:

`SymRunBBBase.lean -> SymRunBBBounds.lean -> SymRunCBFallbackAudit.lean`.

- `SymRunBBBase.lean` contains the isolated generic BB length, numeric-mass,
  and field-maximum helper closure.
- `SymRunBBBounds.lean` proves the BB-sweep length and mass bounds and their
  derived weight/field estimates.
- `SymRunCBFallbackAudit.lean` adds the CB sweep, BB-producing fallback, and
  CB-to-BB-sweep composition.

Pinned run
[45294708124](https://github.com/FlareZ123/bb6/actions/runs/45294708124)
successfully compiled the two original upstream machine modules and
`SymRunBBBase.lean`, then exposed errors in both the older BB length induction
and BB numeric-mass induction.

Pinned run
[45296816853](https://github.com/FlareZ123/bb6/actions/runs/45296816853)
also compiled the original F424/F412 modules and `SymRunBBBase.lean`. Its
axiom audit established that `sweepBB_num_sum_bound` and
`sweepBB_field_max_le` compile without `sorryAx` or `native_decide`.
The overall run nevertheless failed because the older, weaker
`sweepBB_length_bound` induction had unresolved branches: it failed to
convert `L1.length + 1` to the generalized `n` target and had repeat-prefix
list-length associativity mismatches. The dependent
`sweepBB_weight_bound_sharp` therefore still reported `sorryAx` in that
run. The mass and field-maximum theorems did not.

The weaker length theorem is now a direct corollary of the stronger
`sweepBB_length_bound4` theorem. The five diagnosed failures in the earlier
run (two addition-association mismatches and three missing suffix-length
relations) were repaired without changing theorem statements or numerical
constants.

Pinned exact-source run
[45349792391](https://github.com/FlareZ123/bb6/actions/runs/45349792391)
completed successfully at head
`badafa29e69e55025c6490649cba969d49b24018`, using the original F424/F412
modules, Lean `v4.36.0-rc2`, `SymRunBBBase.lean`,
`SymRunBBBounds.lean`, and `SymRunTraceStatsAudit.lean`. The run proves
the BB length, numeric-mass, weight, and field-maximum declarations with no
`sorryAx` or `native_decide`. The printed profiles for
`sweepBB_length_bound4_pair`, `sweepBB_length_bound4`,
`sweepBB_length_bound`, `sweepBB_num_sum_bound`,
`sweepBB_weight_bound_sharp`, `sweepBB_weight_bound_sharper`, and
`sweepBB_field_max_le` are all
`[propext, Classical.choice, Quot.sound]`. Component profiles for
`stepElemBB_num_sum_le` and `peelTok_length_le` are smaller
(`[propext, Quot.sound]`). This is exact imported-source Lean acceptance
for the BB-sweep bounds, not for the later CB fallback or complete
`stepSym` dispatcher.

`SymRunCBFallbackAudit.lean` has now been reached by exact-source run
[45352024498](https://github.com/FlareZ123/bb6/actions/runs/45352024498).
The CB sweep length and numeric-sum bounds, BB-producing fallback length and
numeric-sum bounds, fallback input field estimate, and
`cb_fallback_then_bb_sweep_weight_le_2pow13` all compiled with standard-only
profiles. The sole proof failure was in
`cb_fallback_then_bb_sweep_field_max_le_2pow11`: an in-place simplification
did not expose the left-list projection of the pair-length bound, and the
resulting `omega` goal failed. The printed `sorryAx` for that field theorem
is the failed elaboration artifact, not an accepted result.

The field-bound proof now first derives
`L2.length + R2.length ≤ 570` from the pair bound, then projects
`L2.length ≤ 570`. This narrow repair is commit
`f20740d853e1fd7a6166bd2b3eb3e9d48eb1e848`. A single exact-source retry of
the same bridge is still pending; do not claim the CB field/weight chain
accepted until its field theorem has a clean profile.

The separate 94-token range certificate is present in
`im-results/agent42-cryptids-upstream-191-overlap/SymRunTraceStats.lean`
as 18 F424 and 6 F412 chunk folds plus source checkpoint chains, but the
dossier there still records the exact imported-source compile as pending.
Do not infer a complete blank-root range certificate merely from the
computational replay or checkpoint endpoints.

Acceptance requires successful compilation of the relevant exact-source
dependency closure and exported axiom profiles without `sorryAx` or
`native_decide`. Standard Lean axioms such as `propext`,
`Classical.choice`, and `Quot.sound` are not equivalent to admitting an
unproved theorem.

## Research significance and remaining work

The accepted BB mass and field-maximum inequalities provide a source-generic
bound on numeric-field growth during a BB sweep. The intended combined CB
fallback result would bound the augmented symbolic-state weight by
`2^13*(M+1)` after the CB sweep, BB-producing fallback, and subsequent BB
sweep, conditional on the 94-token premise.

This is a candidate component of a source-certified macro-cost argument, not
a bound on the full `stepSym` transition or blank-root primitive runtime.

Next steps, in dependency order:

1. Exact-compile `SymRunCBFallbackAudit.lean` against the now-accepted
   `SymRunBBBase -> SymRunBBBounds` dependency chain, then audit its
   CB-fallback and CB-to-BB theorem profiles.
2. Exact-compile the 94-token and field-range folds in
   `im-results/agent42-cryptids-upstream-191-overlap/SymRunTraceStats.lean`
   against the pinned F424/F412 source modules; preserve the per-chunk
   all-intermediate-state bounds, not only checkpoint maxima.
3. Connect the accepted BB/CB bounds and range certificates to the actual
   `stepSym` dispatcher and source-native primitive-cost envelope.
4. Audit the complete macro-to-primitive bridge, the initial
   `runElemFast` prefix, and their transitive axioms.
5. Keep all F424/F412 runtime classifications conditional until the original
   one-step and macro-dispatch bridges are kernel-checked.

No claim in this dossier determines BB(6) or proves a universal six-state
upper bound.
