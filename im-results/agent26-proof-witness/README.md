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

## First original-source audit and correction

[Run 45403797219](https://github.com/FlareZ123/bb6/actions/runs/45403797219) failed. All original machine-specific theorem bodies were accessible, but source composition lemmas (`step_stepStar_stepPlus`, `ReachesPlus.trans`, `ReachesPlus.to_star`) reside in the transitively imported Basic module and their bodies were not available to the proof exposer. Importing Basic directly with `import all` addresses this; the next audit must establish acceptance. The upstream casts also use partial-function congruence (`congrFun'`, `congr`). The generalized `liftEq` handles these by accumulating an expression context before specializing the existential predicate, and rejects arbitrary equivalences whose witness-specific predicate cannot be formed.

New local regressions `CongrTest.lean` (nondefinitional equality transports through a curried relation) and `NamedCount.lean` (symbolic sweep of length 2^2000 replaced by its counted lemma without expanding the sweep) both pass Lean 4.36.0-rc2 with only standard axioms. Compile ReachCount.olean before NamedCount.lean. The latter proves the utility of explicit named proof replacement before a potentially intractable unfolding. Source validation remains pending.

## Symbolic affine normalization

[SourceAffineBlocks.lean](SourceAffineBlocks.lean) uses Agent11's original-source SourceCostModel and the upstream stepPure definitions. The tactic normalizes constructor spines for each successive state, generates individual definitional equalities for the state and charge, folds with costIter_local, and leaves only linear arithmetic to omega. It does not use native evaluation or an added axiom. Local preflight against the transcribed pure definitions (same constructor/match bodies, Lean-only imports) proved all 14 formulas in 4.64 seconds, with [propext, Quot.sound] for each. This is a model-level result pending original-source audit. Source file uses exact original imports and no duplicate source definitions. The original source CI should use original_module=BusyBeaver.Calculi.HaltShared, dependency_path=im-results/agent11-symrun-primitive-cost/SourceCostModel.lean, bridge_path=im-results/agent26-proof-witness/SourceAffineBlocks.lean. Primitive-step semantic closure remains a separate obligation.

## Accepted source affine block identities

**Accepted** [pinned-source CI 45406544560](https://github.com/FlareZ123/bb6/actions/runs/45406544560), head 8d4bd6830649cb0b9c5b1a04c66d3d4415a3632d. All fourteen theorems in SourceAffineBlocks.lean compiled against the actual upstream HaltShared and Agent11's SourceCostModel under Lean/Mathlib v4.36.0-rc2; the audit rejects forbidden axioms. This closes the fixed-block arithmetic identities, conditional on primitive-step cost soundness. No full root-time theorem yet.

New drafts: F412CountedPure.lean (exact atoms + six repeated sweeps + pure step), F412CountedSweeps.lean (source sweepBB/CB and elementary dispatcher), F412CountedMacros.lean (closed-form A/B/C iterated costs). These are unaccepted original-source proof designs and depend on the pending F412 atomic audit. Do not import into a trusted coverage certificate until checked.

## Fixed atoms accepted individually, variable normalization correction

[Run 45405871771](https://github.com/FlareZ123/bb6/actions/runs/45405871771) verified all 20 fixed-cost original F412 theorems recovered by Witness.lean: every individual axiom profile is [propext, Classical.choice, Quot.sound]. The overall run failed only for the 3 variable-cost theorems. The actual extracted witness counts agree with the intended 3k, 3d+20, 3d+19. The cyclic induction failed because simp did not normalize nested additions; the two dependent variable-cost theorems timed out while simplifying ReachesIn. Both issues are addressed in 294cdceac90d7a399b91bd37d7a7cc071159fc57 and 92e3760e1457d32c00dc870b8a75b1d535e979a7 by proving an explicit natural-number count equality with omega and rewriting only the count before using the recovered proof. [Run 45408321030](https://github.com/FlareZ123/bb6/actions/runs/45408321030) now tests the repaired atoms and F412CountedPure.lean together.

## Candidate complete exact F412 certificate

[F412CountedDispatch.lean](F412CountedDispatch.lean) is the counted shadow of the original accelerated dispatcher. [F412CountedRoot.lean](F412CountedRoot.lean) adds the MItem prefix, the nested source checkpoint proof chain, and the final physical transition plus first undefined transition. The prefix source-shaped independent replay reached the actual expanded initSymCyc3 state after 19255 elementary transitions, with candidate cost 145981 and maximum run index 85. Combining the previous source replay symbolic cost 9217091204829760959746640857348768637436799 with prefix 145981 and entry/final/undefined 3 gives candidate first undefined index **9217091204829760959746640857348768637582783**. The immediately preceding index is the last defined configuration. These remain computational candidates until the complete proof chain compiles, and no root is counted as formally time-bounded yet.

Use the existing shared manual audit with dependency_path=im-results/agent26-proof-witness/Witness.lean, extra_dependency_path=im-results/agent11-symrun-primitive-cost/SourceCostModel.lean, dependency_manifest=im-results/agent26-proof-witness/RootDependencies.txt, bridge_path=im-results/agent26-proof-witness/F412CountedRoot.lean. The shared workflow now permits an optional, validated ordered dependency manifest (0cbf46ce4a6cc0ebdc00ad74a52e6658bb372b10). Run only after the current focused pure-layer audit returns and any errors are repaired. F424RecoveredAtoms.lean is a separately uncompiled adaptation for the parallel machine; it may solve the two fixed CB cases that resisted the prior handwritten exact-step approach.
