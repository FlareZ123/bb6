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

The weaker length theorem has since been replaced in source by a direct
corollary of the stronger `sweepBB_length_bound4` theorem. Axiom-profile
prints for `sweepBB_length_bound4_pair`, `sweepBB_length_bound4`,
`sweepBB_length_bound`, and `sweepBB_weight_bound_sharper` have been added.
The BB mass induction has also been rewritten explicitly; its successful
axiom profile was already observed in run 45296816853.

The CB fallback proof has been extracted into the third module and includes
the four explicit impossible-mode eliminations in both its numeric-mass and
length arguments. The new length wrapper and CB-to-BB composition have not
yet been kernel-checked. A fresh exact-source run is required before claiming
the complete chain.

Acceptance requires successful compilation of the complete dependency
closure and exported axiom profiles without `sorryAx` or
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

1. Run the updated pinned chain and confirm the stronger BB length theorem,
   its wrapper, the sharper BB weight theorem, and the CB fallback module.
2. Prove the 94-token premise from the F424/F412 blank-start checkpoint
   chains, with kernel-checked range certificates.
3. Connect the accepted BB/CB bounds to the actual `stepSym` dispatcher and
   source-native primitive-cost envelope.
4. Audit the complete macro-to-primitive bridge and its transitive axioms.
5. Keep all F424/F412 runtime classifications conditional until the original
   one-step and macro-dispatch bridges are kernel-checked.

No claim in this dossier determines BB(6) or proves a universal six-state
upper bound.
