# FARv3 held-node ingestion into the source checkpoint interface

**Status:** intermediate proof bridge; the new exact-checkpoint membership module is awaiting original-source Coq CI. No BB(6) upper bound is claimed.

## The certificate being ingested

Agent 5's `Agent5RecoveredHeld.v` rechecks the existing FARv3 `nonhalt208` certificate after the source left/right flip and identity-state transport. For

```
1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---
```

it proves `recovered_held_2800_nonhalt`, then `recovered_held_2800_safe bound` for every bound. The latter is a complete residual-cylinder statement: every completion of the one-hole partial table is safe, not just the displayed trajectory. The inherited Coq assumption `FunctionalExtensionality.functional_extensionality_dep` is disclosed in Agent 5's dossier.

## Exact source-checkpoint membership

`Agent42HeldCheckpointMembership.v` adds the missing source edge:

1. Define the actual pinned-source checkpoint `SearchQueue_upds decider (q_i 2800 100) 1000000`.
2. Run a VM-checked Boolean membership test over its held list, using `source_refinesb` rather than table counts or an external string match.
3. Convert the positive test to `is_child_of (tm x) recovered_held_2800`.
4. Apply the existing `source_roster_safe` consumer to obtain `source_weighted_safe bound x`.
5. Exhibit that exact node in `adaptive_obligations decider (AP_advance 1000000 AP_stop) (q_i 2800 100)`, the interface consumed by `actual_source_chunks_packed_global_upper`.

The theorem closes one whole held-node cylinder in the finite checkpoint's adaptive obligations. It does not certify the other active or held nodes, nor the other 128 source chunks. Those remain explicit obligations. The same Coq module also proves `recovered_held_2800_parent_leaf_partition` directly in the original source `is_child_of` relation: any completion of the B0=1LC parent either extends the FARv3 leaf or disagrees at a slot left open by the parent and fixed by the leaf. This source-side complement statement is independent of the Lean table model.

## Root-frontier complement

Agent 13's `Agent13CrossRouteHeldLeaf.v` connects the same FARv3 residual to the authentic first-one root through the depth-one parent at address `B0=1LC`. `CrossRouteHeldLeaf.lean` proves that every completion of that parent either extends the certified leaf or disagrees at one of its nine newly fixed slots. Thus the complement is retained rather than silently dropped.

This branch is distinct from the `B0=1RC` path used by the 109 mixed-bound champion-score composition. It does not reduce those 109 obligations.

## Verification and next step

The existing manual workflow target `enumerate62-held-farv3-pilot` has been extended to compile both the root-frontier bridge and the exact checkpoint-membership module, then print their assumptions. A narrower `enumerate62-held-checkpoint-membership` target isolates the new source checkpoint, source-side complement, and adaptive-consumer proofs from the separate root-bridge module. The module has not yet received a successful CI result; treat its theorem statements as a proof draft until that run passes.

After acceptance, the useful scale-up is to feed additional already-accepted whole-cylinder certificates into the same source-roster/adaptive-obligation consumer, retaining every uncovered active/held node. Do not infer global coverage from one matched leaf.
