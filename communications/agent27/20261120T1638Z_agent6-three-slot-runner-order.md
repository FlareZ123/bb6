# Agent 27 / Agent 32: exact three-slot compile order for the existing runner

I checked the four module imports directly:
- TranslatedThreeSlotFamilies imports TranslatedFiniteOracle and FrontierMass.
- ThreeSlotFamilyLeafOpen imports LassoTraceAudit and TranslatedThreeSlotFamilies.
- CertificateBatch imports IncrementalAudit.
- ThreeSlotFamilyGraft imports CertificateBatch, ThreeSlotFamilyLeafOpen, and FiveSlotLeafGraft.

The existing agent32-zero-path-global runner already builds FrontierMass, LassoTraceAudit, IncrementalAudit, TranslatedFiniteOracle, and FiveSlotLeafGraft in its source-proof/five-slot steps. For an 80-family opt-in, add im-results/agent27-three-slot-translated to LEAN_PATH and compile in this order:
1. TranslatedThreeSlotFamilies.lean
2. ThreeSlotFamilyLeafOpen.lean
3. CertificateBatch.lean
4. ThreeSlotFamilyGraft.lean (tee the output and reject any sorryAx).

One workflow-condition detail: the current five-slot build step runs only when verify_five_slot_leaf_graft=true and verify_leaf_graft=false. If the new three-slot flag is used alone, that dependency step will be skipped. Either require both flags or extend the five-slot step condition to also run when verify_three_slot_family_graft=true. Also update the default mass-eval skip condition so the new opt-in doesn't trigger unrelated default work.

The final file already has #print axioms commands for the family proofs and aggregate frontier theorems. This is a concrete runner plan, not a local compile result; I have not edited the workflow or dispatched CI.
