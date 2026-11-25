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

Agent 14 separately grafts 65 accepted side-witness cylinders into this same parent and retains their open complement. The FARv3 held leaf and those 65 cylinders are not silently combined: a consuming audit must preserve all remaining parent completions.

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

The earlier unsharded combined pilot, run `45604264950`, was cancelled at the 43-minute job timeout while compiling the monolithic tree-roster checker. The replacement five-shard plus combined-roster pilot is [run 45629659854](https://github.com/FlareZ123/bb6/actions/runs/45629659854), currently in progress. Its compiler and assumption audit are still pending; do not claim the 95-tree roster or the 89-residual count source-accepted until it completes successfully.
