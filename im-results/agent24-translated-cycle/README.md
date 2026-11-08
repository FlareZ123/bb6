# A sound translated finite-tape cycle oracle for the six-state frontier

**Agent 24, 8 November 2026. Status: complete original-source Lean-verified intermediate theorem.** This is a genuinely new sufficient certificate in the repository's machine-classification toolset. It does **not** resolve any historical six-state holdout, establish a universal BB(6) bound, or determine BB(6).

## The complete-configuration theorem

For the unmodified `BB6Coverage` primitive-step semantics, the theorem `translated_cycle_iter` in [TranslatedCycle.lean](TranslatedCycle.lean) proves, for every machine `m`, configuration `c`, positive or zero period `p`, translation `d:Int`, and `k:Nat`:

```
run m p c = some (shiftConfig d c)
  =>
run m (p*k) c = some (shiftConfig (d*k) c).
```

When `p>0`, `translated_cycle_live` proves every finite step from `c` remains live. When a genuine blank-tape prefix reaches `c`, `translated_prefix_never` proves `NeverHalts m`. This covers nonzero spatial displacement and also the ordinary exact-lasso special case `d=0`. The result reuses the **unchanged, previously source-verified** [RootShift.lean](../agent8-coverage-contract/RootShift.lean) translation equivariance and raw-run composition lemmas.

[TranslatedFiniteOracle.lean](TranslatedFiniteOracle.lean) implements an executable *exact* finite-support comparison. It checks identical control states and bidirectional equality of the sets of marked cells after translation by the head displacement, handling duplicate list entries correctly. Its theorem `shiftedFiniteEq_sound` equates the complete infinite tapes as functions on every integer location. The all-completions theorem `finiteTranslatedCheck_sound` transports two successful sparse physical traces into an all-time `Cover (DecidedBelow bound) p` certificate.

No hash fingerprints, finite-run extrapolation, assumed invariants, novel axioms, or unverified tape-completion assumptions enter these soundness proofs.

## Concrete strictly additional nonhalting cylinder

The seven assigned actions in `movingPairTable` are:

```
A/0 = 1RF
B/1 = 0RC
C/1 = 1RD
D/0 = 1LE
E/1 = 1RF
F/0 = 1LB
F/1 = 1LB
```

All five other state/symbol entries remain completely unrestricted. The blank machine writes adjacent ones at tape locations 0 and 1, then enters B at location 0 after two ordinary moves. Every subsequent five moves return to B with two adjacent ones and head moved exactly one place right. Thus there is a literal translated complete-tape cycle with `entry=2`, `period=5`, `offset=+1`; the original ordinary machine never halts, for **every one of `25^5=9,765,625` full-table completions**. The facts are independently Lean-certified by `movingPair_check`, `movingPair_never`, and `movingPair_cylinder_mass` in [TranslatedSeparation.lean](TranslatedSeparation.lean).

Importantly, the existing combined sufficient predicate `lassoDecisionOracle movingPairTable 6 12 12 12 12` is **provably false**, whereas the new translated decision predicate is true. `movingPair_old_combined_misses` is kernel-checked Boolean computation on the unchanged previous original-source oracle. This proves strict inclusion of accepted **partial tables** at those explicit search bounds; it does not claim that none of the full-table completions could be resolved by an alternative certificate or by a deeper global audit.

## Integration with the exhaustive-or-open census

[TranslatedFrontier.lean](TranslatedFrontier.lean) introduces:
- `finiteTranslatedOracle`: discovers any positive period within a bounded range after any bounded physical blank prefix.
- `translatedDecisionOracle`: disjoins the new certificate with the unchanged previous original-source finite-halt, clean-ray, zero-mask, finite-lasso, and finite-entry ray-macro predicate.
- `translatedPhysicalTraceAudit`: branches only on the first genuinely consulted unassigned read-zero **or read-one** input, using the original sparse-machine semantics.

The exact `globalTranslatedPhysicalTraceAudit_exhaustive` and `globalTranslatedPhysicalTraceAudit_conserves` theorems show that every complete `25^12` raw table either has a real sound score-at-most-six/nonhalting certificate or remains in a visibly open leaf, with total mass conserved. The globally interpreted numeric certified count has **not** been calculated; no additional percentage is asserted. The translation discovery limits do not bound the future behavior of a certified machine.

## Reproducibility and limitations

The manual-only [original-source workflow](../../.github/workflows/agent24-translated-cycle.yml) compiles the unchanged `Frontier`, `RayFinite`, `Symmetry`, `RootShift`, `FiniteLassoOracle`, `EntryMacroLeft`, `LassoTraceAudit`, and `FrontierAudit` dependencies under Lean 4.36.0-rc2 before compiling these four new Lean modules. All key `#print axioms` audits are included. Three successive manual CI runs passed:
- [42534456051](https://github.com/FlareZ123/bb6/actions/runs/42534456051): complete source-backed translation theorem and first checker;
- [42534766956](https://github.com/FlareZ123/bb6/actions/runs/42534766956): the two-marker convoy, strict original-oracle separation, and cylinder mass;
- [42534914962](https://github.com/FlareZ123/bb6/actions/runs/42534914962): full soundness and exhaustiveness integration.

The original scientific aim remains an unresolved-root theorem. A direct finite simulation using translation-normalized two-prime support hashes found no translated-cycle candidates among all 663 historical 16 October 2026 holdouts in their first 20,000 raw moves. This observation is a **bounded negative experiment**, not a proof of the absence of longer translated periods, and no historical holdout has been newly decided. A source-specific invariant, a richer macro, or a genuinely new root result is needed to move the BB(6) frontier beyond this generic certificate family.
