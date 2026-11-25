# Canonical76 raw10 seven-rectangle consumer

## Scope

`Canonical76Raw10Boxes18to24Consumer.lean` connects three existing pieces:

- Agent31's `CanonicalTwoParentRosterOnly.exact_at_target`, the exactness interface for the 76-residual roster;
- Agent50's `Canonical76Raw10Membership`, which identifies the B0=1LC raw10 parent inside that roster;
- Agent49's `Raw10Box18to24CombinedBridge`, which consumes seven source-certified rectangles at weighted bound 598 inside the 41-box raw10 remainder.

The new theorem `BB6.Agent13Canonical76Raw10Boxes18to24Consumer.exact_at_champion_score` is conditional. It requires:
1. a weighted Cover for each of the 34 boxes in the false-match complement of the seven certified rectangles; and
2. a weighted Cover for each of the other 75 canonical76 representatives.

It then supplies the raw10 parent Cover and invokes the 76-way exactness theorem with the established champion witness. It does **not** close the 34 boxes or the other 75 representatives, and it is not an unconditional BB(6) upper bound.

## Source and evidence

- Seven raw10 rectangles (original source indices 19, 18, 17, 8, 6, 3, 2) have original-source Lean bounds at 598; Agent49's source run 45690247771 compiled the seven-rectangle source module.
- Agent17's source-identity bridge run 45702115754 checked the 66 encoded rows and all 34 indexed boxes against `Raw10BoxCore.raw10Remainder`.
- The combined 41-box parent bridge and this canonical76 consumer still require a single source-closure audit. The held-leaf-only run 45695751601 was cancelled at its 60-minute job timeout, before reporting a theorem failure.
- The source-audit target is `weighted-tnf-raw10-box18to24-canonical76`. Run 45708612868 is queued on workflow commit `f66bb769ddc68af6185bc386b0f8710bf0d28626`. Earlier attempts 45706076088, 45706673886, and 45707508626 stopped in precompiled-artifact path/manifest setup, before Lean compiled the new consumer.

## Next work

1. Complete run 45708612868. Its precompiled directory merges the canonical77 certified objects with the raw107 shared-core objects, using both manifests and checking each object path.
2. If Lean rejects the consumer, fix the concrete type/import/proof issue and rerun the same target.
3. On success, preserve the source artifact and exact axiom profile, then integrate the 34-box interface into the wider raw10 and canonical76 synthesis.
4. Do not repeat the 34-box singleton-projection scan: Agent17 already checked all 34 boxes and obtained zero certificates for that specific generator. Pursue domain-preserving/set-valued methods or source-accepted upstream covers instead.

This file is an intermediate research record and therefore belongs in `im-results/`, not `results/`.
