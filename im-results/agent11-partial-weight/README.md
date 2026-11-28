# Exact weighted-threshold semantics for partial Busy Beaver audit trees

**Status:** Lean source candidate; original-source audit dispatched as [CI 46146755553](https://github.com/FlareZ123/bb6/actions/runs/46146755553). Do not promote to `results/` until the exact transitive source closure and standard-axiom audit pass.

## Mathematical contribution

The repository uses `PartialAudit` trees to certify large six-state machine cylinders. A node is either `unresolved`, a completely checked `Audit` subtree, or a first-unassigned-slot split across all 24 nonhalting transitions. The previously accepted checker `partialCheck A p t = true` certifies the shape, all first-query traces, and nonhalting leaf evidence at a coarse weighted threshold `A`; `partialResiduals p t` explicitly records every unresolved cylinder.

The generic `Agent32AuditReweight.partialWeights B p t` checks **only** the possible incoming-blank-delay surcharge at each reachable first-query node; it skips all runs, cycle witnesses, FAR automata, and semantic proofs. `partial_reweight` previously established sufficiency to transfer an accepted `partialCheck A` certificate to a new threshold `B`.

The new file [PartialWeightExact.lean](PartialWeightExact.lean) supplies the missing necessary direction, for arbitrary natural numbers `A` and `B`:

1. **Necessity.** If *all* full machines compatible with `p` satisfy `WeightedBound B`, then `partialWeights B p t = true`, provided the original partial audit was accepted. Proof: induction over the partial audit, applying the generic previously proved `ZipWeightTighten.queryWeight_complete` lemma at every split and `weights_complete` structure at full audits. The crucial soundness condition is that each audit split follows an actual visited unassigned slot.
2. **Exact decision under residual evidence.** Suppose every explicitly retained partial residual has a separate `WeightedBound B` theorem, and the parent satisfies the standard `firstOne` and no-assigned-halt preconditions. Then
   ```lean
   (∀ m, compatible p m → WeightedBound B m)
     ↔ partialWeights B p t = true
   ```
   The reverse direction composes `partial_reweight` with `partialSound`, using the residual hypotheses rather than discarding them.

The result means a previously authenticated large partial audit need **never rerun tape simulation or automata proofs** to identify its exact weighted threshold, once each residual is independently bounded. It makes the bound check *complete*, not only sound. The proof uses the original machine-compatibility semantics and no additional axiom.

## Proposed applications and limits

- **Raw112.** The six-hole parent `1RB---_1RC---_0RD---_1LD1RE_---1LC_------` has a generated `PartialAudit` with 25,004 split nodes and 446,232 cycle nodes and only two final nonhalting residual families, both source-certified. Once the 100,000-bound parent source proof is integrated, `partialWeights B parent tree` can be checked against its identical original source and the two nonhalting residual Covers at any candidate `B`. This may produce a sharper *whole-cylinder* bound. A **separate attaining halter witness** is still necessary to assert the minimum or exact maximum.
- **Other hard cylinders.** This theorem handles unresolved-frontier trees uniformly, regardless of which external nonhalting strategies close the residuals. It can reuse accepted `AuditReweight` data, unlike a new run of the expensive original analysis.
- **Global BB(6).** This is a local proof technique. It does not itself close a new cylinder, remove a canonical residual, or determine BB(6). Any numerical bound improvement must be linked to original-source Lean acceptance before publication.

Reproduce with `shared-lean-source-closure.yml` inputs `root=im-results/agent11-partial-weight/PartialWeightExact.lean`, `theorem_suffix=.partial_weights_exact`, `minimum_theorems=1`, `preparation_profile=none`. On success inspect both compiler and axiom profiles; no sorryAx/native_decide admitted.
