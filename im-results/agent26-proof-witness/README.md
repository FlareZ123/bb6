# Recovering counted reachability from existing constructive proofs

**Scope:** proof-generation infrastructure. The local regression passes Lean 4.36.0-rc2; the F412 original-source experiment is a draft pending pinned-source acceptance. This is not a machine decision or a BB(6) bound.

The metaprogram in [Witness.lean](Witness.lean) unfolds theorem proof values in the elaborator, exposes an `Exists.intro` constructor, and returns the proof at its recovered witness. For existential-positive reachability it takes the second conjunct. Ordinary congruence transport is lifted to the predicate at that witness. Every generated theorem is checked by Lean; proof-term search is not a new trust assumption. Arbitrary proposition equivalences are **not** assumed witness-preserving.

The command `recover_count old_theorem as new_theorem positive` generates the counted theorem with the original binders. For symbolic induction, `witness_proof% (old_term) using [replacement]` accepts a definitional existential proof reconstructed from the counted induction hypothesis, so a gigantic repetition need not be unfolded. The replacement must prove exactly the required proposition. When replacement is used, the result is a certified witness, not necessarily the witness originally chosen by the opaque proof.

## Local regression

```sh
lean -o Witness.olean Witness.lean
lean -o ReachRules.olean ReachRules.lean
LEAN_PATH=. lean ReachCount.lean
```

The imported model tests fixed and rewritten compositions and the symbolic n-step sweep on arbitrary left/right lists. All three named regression theorems had only [propext, Quot.sound]; the automatically recovered single-step theorem had no axioms. The module-system private-import experiment also recovered an otherwise private existential theorem using `module; meta import Witness; import all Private`.

## Original-source target

[F412RecoveredAtoms.lean](F412RecoveredAtoms.lean) applies the approach to the pinned `google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a` F412 machine. The 20 fixed rules (including entry, exit and final physical halt transition) are recovered from the actual proofs; the counted cycle is supplied as a symbolic induction replacement to the two variable-cost rules. This complements the existing Agent11/Agent42 cost effort. Expected variable costs are 3d+20 and 3d+19.

Local Lean itself is functional, but the exact upstream Mathlib/source checkout cannot be cloned in this container (DNS resolution fails for github.com). Use the existing shared manual source audit, with dependency Witness.lean and bridge F412RecoveredAtoms.lean, pinned Lean/Mathlib v4.36.0-rc2. The bridge uses `import all` to access private source declarations without changing source bodies or visibility. No exact upstream proof claim until that audit succeeds.

## Limitations

The exposer is intentionally incomplete: arbitrary logical equivalences, opaque assumptions without supplied witness proofs, unsupported eliminators, and fuel/time limits may prevent recovery. A failed extraction is not a mathematical counterexample. Even accepted atomic counts do not prove the full accelerated dispatcher or the blank-root halting-time bound. The larger source arithmetic and trace are maintained by Agents 11/38/42.
