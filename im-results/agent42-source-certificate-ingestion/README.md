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


## q2800 95-tree roster and conditional global interface — source acceptance pending

The q2800 checkpoint's 95 source-tree certificates have been moved into `Agent42Q2800BatchData.v` and split across `Agent42Q2800BatchShard01.v` through `Shard05.v`. Each shard contains an independently checked `vm_compute` theorem. The aggregator `Agent42Q2800BatchWitnesses.v` combines those theorems with `forallb_app`, then derives the tree-roster safety theorem, adds the exact held leaf, and computes the residual obligations. The shard partition contains all 95 original rows exactly once. It changes the roster's list order to balance estimated checker work; the source checkpoint obligation order remains unchanged and the coverage predicate is order-independent.

The approximate checker weights of the five groups are 1455, 1449, 1454, 1514, and 1568 (30, 29, 30, 3, and 3 source-tree roots respectively). This is a compile-time decomposition, not a new mathematical assumption.

`Agent42Q2800GlobalUpper.v` packages the intended chunk-28 reduction. Its theorem assumes that the 89 residual obligations left after the 95 tree certificates plus the exact held leaf are safe, and that the other 128 source chunks are safe. It then derives the existing global source upper interface. **It does not prove those residual or other-chunk premises and is not a BB(6) upper-bound proof.** The 89 count and all tree checks remain pending source acceptance until the sharded `enumerate62-held-farv3-pilot` target compiles and its assumption audit completes.

The earlier unsharded combined pilot, run `45604264950`, was cancelled at the 43-minute job timeout while compiling the monolithic tree-roster checker. The new five-shard target has been wired into the existing manual workflow but has not yet been dispatched.

The independent held-node consumer target has been decoupled from the tree roster so it can be audited on its own. Run `45624293740` compiled and printed assumptions for `Agent42HeldCheckpointMembership`, then failed in the downstream consumer due missing direct namespace imports. Those imports have been corrected; a third retry has been dispatched, but its run ID/status is not yet confirmed because the Actions run-list endpoint is rate-limited. Do not claim the consumer theorem accepted until a run compiles `Agent14HeldQueueConsumption.v` and completes the theorem-assumption audit.

The membership audit output includes Coq primitive-array (`PArray`) axioms and `LibTactics.inj_pair2`; these are dependencies of the original-source queue implementation and should be disclosed, not silently described as an axiom-free computation.
