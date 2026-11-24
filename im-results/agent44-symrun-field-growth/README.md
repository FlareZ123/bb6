# SymRun symbolic-state growth and field potential

This dossier develops exact-source growth bounds for the symbolic-run engine
in `google-deepmind/cryptids` at commit
`3647718b5df22e1a61462dec0376bd204526285a`. The audited machine modules are
F424 and F412, compiled with Lean `v4.36.0-rc2`.

## Mathematical statements under development

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
`W = 1 + |L| + |R| + numSum(L) + numSum(R)`, the weight statement gives
`W_out <= 7*W_in + 11 <= 9*(W_in + 1)` for `W_in >= 1`. This is a
source-generic BB-sweep bound, not yet a bound on the full `stepSym`
transition or blank-root primitive runtime.

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

These are conditional symbolic-state inequalities. They do not by themselves
establish the 94-token invariant for a blank-start trace, prove the complete
`stepSym` dispatcher, or classify F424/F412 primitive runtime.

## Exact-source modules and current CI status

The dependency chain is:

`SymRunBBBase.lean -> SymRunBBBounds.lean -> SymRunCBFallbackAudit.lean`.

- `SymRunBBBase.lean` contains the isolated generic BB length, numeric-mass,
  and field-maximum helper closure.
- `SymRunBBBounds.lean` proves the BB-sweep length and mass bounds and their
  derived weight/field estimates.
- `SymRunCBFallbackAudit.lean` adds the CB sweep, BB-producing fallback, and
  CB-to-BB-sweep composition.

Pinned run [45294708124](https://github.com/FlareZ123/bb6/actions/runs/45294708124)
successfully compiled the two original upstream machine modules and
`SymRunBBBase.lean`, then failed in the earlier version of
`sweepBB_num_sum_bound`. The errors exposed missing final induction steps
from `L1.length + 1 = n`, repeat-counter normalization in the failed-prefix
branches, and associativity normalization in the recursive repeat branches.

Those BB mass-induction cases have now been rewritten explicitly. The
four impossible CB-to-BB mode branches in both
`stepElemCB_BB_num_sum_le` and `stepElemCB_BB_length_bound` have also been
made explicit by reducing the mode hypothesis and eliminating the impossible
constructor equality. The broad `SymRunTraceStats.lean` module itself remains
unaccepted and is not imported by this isolated dependency chain.

The current pinned audit is
[45296816853](https://github.com/FlareZ123/bb6/actions/runs/45296816853),
using the exact upstream SHA above, Lean `v4.36.0-rc2`, and the full
Base -> BB bounds -> CB fallback audit chain. Its result is pending; none of
the statements in this dossier should be treated as kernel-accepted until
that run and its transitive axiom profiles pass.

Acceptance requires successful compilation of the complete dependency
closure and exported axiom profiles without `sorryAx` or
`native_decide`. Standard Lean axioms such as `propext` and
`Quot.sound` are not equivalent to admitting an unproved theorem.

## Research significance and remaining work

The potential estimates offer a reusable way to bound symbolic-run state
growth without enumerating every represented primitive transition. The BB
sweep has a linear augmented-weight bound; the CB-to-BB fallback has a
conditional maximum-field bound with factor `2^11` after the subsequent BB
sweep. This is a candidate component of a source-certified macro-cost
argument, not a universal upper bound for six-state machines.

Next steps, in dependency order:

1. Finish the current pinned compile and repair only the first concrete Lean
   failure.
2. Establish the 94-token premise from the F424/F412 blank-start checkpoint
   chains, with kernel-checked range certificates.
3. Connect the accepted BB/CB bounds to the actual `stepSym` dispatcher and
   source-native primitive-cost envelope.
4. Audit the complete macro-to-primitive bridge and its transitive axioms.
5. Keep all F424/F412 runtime classifications conditional until the original
   one-step and macro-dispatch bridges are kernel-checked.

No claim in this dossier determines BB(6) or proves a universal six-state
upper bound.
