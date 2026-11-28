# Canonical40 → Canonical39 by the complete Raw39 parent

**Status:** source-accepted Lean 4.36.0-rc2 result.

## Result

The accepted Canonical40 quotient can be reduced by one whole parent using the
complete Raw39 proof.  Let `roster40` denote
`BB6.Agent31Canonical40Extra57.roster40`, the accepted 40-representative
quotient after the Raw57 reduction.  The Raw39 partial machine occurs exactly
once in that roster, and every compatible completion of Raw39 has weighted
halting cost at most **28,311**.  Therefore Raw39 is covered at the champion
threshold 6,766,859 and can be removed.

The resulting source theorem
`BB6.Agent11Raw39Canonical39Successor.sound_integrated` states that every
blank-compatible six-state machine is either bounded by
`WeightedBound 6766859` or is TNF-quotient-compatible with one of exactly
**39** retained representatives.

Consequently,
`BB6.Agent11Raw39Canonical39Successor.exact_at_champion_score` proves exact
BB(6) at the proposed champion score conditional only on champion-score Covers
for those 39 retained representatives.

This is a strict one-lineage reduction from the accepted Canonical40
predecessor; it does not add or splice residual counts from independent
quotient branches.

## Source acceptance

GitHub Actions run **46129131784**, job **140930242887**, completed successfully
on 2026-11-28.  The accepted evidence artifact is:

- artifact **15258350500**
- name `raw39-global-source-global-parent-chunked`
- SHA-256 `aa5706bd0657478d66b1707bdd16e73101047e6f26206157c91f8312035d4557`
- source checkout `6d5196868ae0d95c217b54a308550b9bfd5572ba`

The run authenticated all eleven Raw39 child proof producers, rebuilt the exact
Raw39 whole-parent bound **28,311**, restored the accepted Canonical40
predecessor, kernel-checked the compatible Raw39 proof-object transport, and
source-compiled the final quotient theorem.

The audited transitive axiom profiles for the final bridge and successor use
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
In particular the successful log reports:

- `BB6.Agent11Raw39Canonical40Bridge.weighted_cover`
- `BB6.Agent11Raw39Canonical39Successor.count39`
- `BB6.Agent11Raw39Canonical39Successor.sound_integrated`
- `BB6.Agent11Raw39Canonical39Successor.exact_at_champion_score`

all with no `sorryAx` or `native_decide` dependency.

## Scope

This result does **not** determine BB(6).  It removes one universally covered
parent from the accepted 40-representative universal quotient and leaves 39
explicit Cover obligations.  Further exact-lineage reductions are required
before the champion lower bound becomes a universal upper bound.
