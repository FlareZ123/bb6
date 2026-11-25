# FARv3 held-node ingestion into the source checkpoint interface

**Status:** intermediate source-queue integration; the held-node cylinder is certified, and its exact finite source checkpoint is independently reproducible. The complete root Cover and BB(6) upper bound remain open.

## The certified cylinder

The source table

```
1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---
```

is the one-hole held node at `q_i(2800,100)`. Agent 5's `Agent5RecoveredHeld.v` reflects it to the existing FARv3 `nonhalt208` certificate and proves `recovered_held_2800_safe bound` for every bound. This is a whole-cylinder nonhalting result, not merely a trajectory replay. The inherited Coq primitive/functional-extensionality assumptions are disclosed in Agent 5's source dossier.

## Exact source checkpoint

The original-source batch run [45525114781](https://github.com/FlareZ123/bb6/actions/runs/45525114781), pinned to BusyCoq revision `33209bc7dc282b38c8cd6be507bfc551fea56108`, computed `SearchQueue_upds decider (q_i 2800 100) 1000000` and emitted the packed module `Agent8Batch_2800_100_1000000`.

Its exact result has **184 active nodes and one held node**. The held node is exactly the FARv3 table above. The generated `chunk_data_exact` theorem proves equality of the original source queue with the decoded packed checkpoint; the queue computation completed in about 46 seconds. The proof depends only on the original source's disclosed `PrimInt63`/`PArray` computational primitives and their correctness assumptions.

The current integration avoids repeating that computation inside a nested membership test. The existing manual workflow first generates and compiles the packed checkpoint once, then `Agent42HeldCheckpointMembership.v` imports its proof-carrying `.vo` and checks the decoded held list. The theorem `recovered_held_2800_checkpoint_exact` transports that membership back to the actual original-source queue. The membership predicate is exact transition-table equality, not a count or string-only match.

## Parent and complement

The exact B0=1LC parent is

```
1RB---_1LC---_------_------_------_------
```

It is a retained member of the 109-entry weighted first-one roster (canonical index 6). The source theorem `recovered_held_2800_parent_leaf_partition` proves that every completion of this parent either extends the FARv3-certified leaf or disagrees at a slot fixed by the leaf and left open by the parent. The complement is therefore explicit and retained.

The 65 side-witness cylinders are now combined with the q2800 held leaf, the cycle-return cylinder, and the forced-halt cylinder in the exact four-family partition `Agent13HeldBlockRaw10Combined`. The partition retains all 41 complement boxes; the held leaf has an independent Lean BlockFAR proof (`Agent13HeldBlock.held_weighted`). The weighted 109-roster composition below consumes this entire partition rather than silently dropping any parent completion.


## B0=1LC weighted 109-roster composition — CI pending

The new intermediate Lean module `Agent42B01LC109SourceConsumer.lean` composes three existing formal interfaces:

1. `Agent14B01LC109Graft.otherRoster`: the 108 entries of the 109-entry mixed-bound roster other than the exact B0=1LC parent;
2. `Agent13HeldBlockRaw10Combined.raw10_cover_with_cycle_and_halt`: a weighted cover of that exact parent from the four certified families and the 41 exact complement boxes;
3. `MixedBound109Composition.exact_from_reduced_roster_at_champion_score`: the existing champion-score exact-BB(6) composition.

Its theorem `exact_from_108_and_41_boxes` is conditional: if all 108 other roster entries and all 41 retained complement boxes are covered at the attained champion score, then `ExactBB6` follows. The parent completion mass is 95,367,431,640,625; the four certified families account for 4,629,927,926,900 completions; the remaining 41 boxes account for 90,737,503,713,725. The refined unresolved frontier is therefore 108 other entries plus 41 boxes (149 obligations), not a closed BB(6) proof.

The q2800 held leaf is included in the four-family cover through the Lean BlockFAR theorem `Agent13HeldBlock.held_weighted`, not merely through the separate Coq FARv3 source certificate. The exact complement is formalized by `raw10RemainderWithCycleAndHalt_exact`; the weighted cover is `raw10CoverWithCycleAndHalt`.

CI history:
- Base run [45651264742](https://github.com/FlareZ123/bb6/actions/runs/45651264742) exposed a Lean 4.36 parser error in `RootRaw10Core.decodeMove` (record literal fields `right` and `next` were rejected). The branch patch replaces the record literal with the `Move` constructor.
- Full retry [45653497419](https://github.com/FlareZ123/bb6/actions/runs/45653497419) includes that fix and the new composition module; it is still compiling. The extended axiom audit now also requires the exact parent-partition, held-leaf, and weighted-cover theorem profiles. Because that audit extension landed after run 45653497419 started, a successful run should be followed by a precompiled-closure run using input `b0_1lc_base_run_id=45653497419`.
- Until the compile and extended audit pass, treat this as a proposed composition, not a CI-accepted result.

The source-queue consumer above remains a separate route: it discharges one exact source-held-table obligation but does not itself establish the weighted 109-roster parent cover.

## Source consumer and scope

`Agent14HeldQueueConsumption.v` filters only exact copies of the FARv3 table from the adaptive obligation list. A generic `Forall` partition theorem proves that the original list is safe exactly when the filtered residual list is safe, since every removed occurrence is covered by the whole-cylinder certificate. The packed global-upper consumer then leaves all other 128 source chunks unchanged.

The resulting theorem remains conditional on:
- exact packed checkpoint equations for all 129 source chunks;
- weighted safety of every remaining active/held node after the one exact-table filter;
- the global source-queue coverage and normalization hypotheses.

Thus this pilot discharges one held table's safety obligation but does **not** close the B0=1LC parent, reduce the 109 count by itself, or prove a universal BB(6) upper bound.

## Reproduction and acceptance

Use the existing manual workflow `.github/workflows/shared-rocq-root-proofs.yml`:
- `enumerate62-held-farv3-pilot`: original-root bridge plus packed-checkpoint membership;
- `enumerate62-held-checkpoint-membership`: isolated membership/source checkpoint proof;
- `enumerate62-held-checkpoint-consumption`: exact-table filter and conditional global consumer.

The packed checkpoint is generated with the existing `export-source-batch.sh` at range `2800:100:1000000`; its exact `.vo` is consumed within the same run. The end-to-end membership/consumer audit is pending on the current revision. The earlier direct-membership run 45557567037 was cancelled during compilation without a proof diagnostic; it is superseded by this shared-checkpoint path.

Keep this material in `im-results/`: it is useful proof integration, not an unconditional mathematical result.


## q2800 95-tree roster and combined source interface — sharded CI pending

The q2800 checkpoint's 95 source-tree certificates have been moved into `Agent42Q2800BatchData.v` and split across `Agent42Q2800BatchShard01.v` through `Shard05.v`. Each shard contains an independently checked `vm_compute` theorem. The aggregator `Agent42Q2800BatchWitnesses.v` combines those theorems with `forallb_app`, then derives the tree-roster safety theorem, adds the exact held leaf, and computes the residual obligations. The shard partition contains all 95 original rows exactly once. It changes the roster's list order to balance estimated checker work; the source checkpoint obligation order remains unchanged and the coverage predicate is order-independent.

The approximate checker weights of the five groups are 1455, 1449, 1454, 1514, and 1568 (30, 29, 30, 3, and 3 source-tree roots respectively). This is a compile-time decomposition, not a new mathematical assumption.

### Exact cross-route and combined roster

Agent 5's generic source-held roster was already accepted in [run 45608313328](https://github.com/FlareZ123/bb6/actions/runs/45608313328). In `Agent42Q2800GlobalUpper.v`, I now explicitly construct the Agent 5 q2800 held attempt, check that it passes `held_check`, and prove `recovered_held_2800` belongs to `held_certified_roster`. Together with `recovered_held_2800_checkpoint_leaf`, this gives an exact table-level theorem: the same machine is a leaf of the original `q_i(2800,100)` checkpoint and a member of Agent 5's accepted source-safe roster. The table is `1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---`.

The new combined roster is
`q2800_augmented_roster := held_certified_roster ++ q2800_tree_roster`.
Its safety follows by `Forall_app` from Agent 5's held-roster theorem and Agent 42's q2800 tree-roster theorem. The new global interface specializes Agent 5's generic `roster_filtered_global_upper`: it filters every one of the 129 source chunks using exact `source_roster_covers` refinement by the union roster. Its remaining-obligation premises are conditional; it does not prove the remaining machines safe and is not a BB(6) upper-bound proof.

The separate Agent 14 q2800-only consumer is redundant with Agent 5's already accepted generic `roster_checkpoint_consumption` / `roster_filtered_global_upper` route. Its latest run, [45625068546](https://github.com/FlareZ123/bb6/actions/runs/45625068546), failed in the duplicate `Forall_filter_partition` proof at line 30. Do not spend further compute repairing that duplicate unless it acquires a distinct purpose. Agent 42's exact checkpoint-membership module compiled and its assumption audit ran in [45624293740](https://github.com/FlareZ123/bb6/actions/runs/45624293740); its printed dependencies include Coq primitive-array (`PArray`) axioms and `LibTactics.inj_pair2`, which must be disclosed rather than calling the computation axiom-free.

The earlier unsharded combined pilot, run `45604264950`, was cancelled at the 43-minute job timeout while compiling the monolithic tree-roster checker. The unsharded combined pilot [45629659854](https://github.com/FlareZ123/bb6/actions/runs/45629659854) was canceled at the 43-minute timeout. The replacement uses `q2800_shards.py` and separate shard01..05 workflow targets. First attempt [45649454225](https://github.com/FlareZ123/bb6/actions/runs/45649454225) exposed a missing direct `SourceResidualRoster` import in `Agent42Q2800BatchData.v`; that import is now fixed (source commit `5e00f3c7dc2959b6ad155b2e875d0881af1c53e3`). Shard01 [45649689177](https://github.com/FlareZ123/bb6/actions/runs/45649689177) is still compiling on branch `agent42-q2800-shards-v2-20261125`. Do not dispatch shards 02..05 until shard01 and its strict manifest pack pass. The 95-tree roster and 89-residual source-queue count remain unaccepted until all five shards and the assembler pass.
