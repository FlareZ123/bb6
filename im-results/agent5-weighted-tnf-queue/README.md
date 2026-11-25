# Enumerate62 q0 source-queue export and adaptive coverage

**Status (2026-11-25): intermediate computational work; no BB(6) upper bound has been proved here.**

This directory tracks the bridge from the original Coq Enumerate62 source queue to the source-root coverage work in `im-results/agent32-source-queue/`. The immediate missing object is a reproducible export of the 129 q0 chunk checkpoints and the exact residual obligations they leave.

## Established components

- `Agent5Enumerate62DeciderSound.v` passed CI run `45414978702`. It proves soundness of the actual source `decider` branches against the original Coq machine semantics. This is a semantic adapter, not a complete classification of all residual machines.
- `im-results/agent8-adaptive-source-plan/Agent8QueueCheckpoint.v` defines the packed queue encoding and the exact `source_checkpoint_decode` theorem.
- `im-results/agent8-adaptive-source-plan/Agent8AdaptiveSource.v` provides finite-checkpoint and adaptive-plan soundness, including the active-plus-held residual interface. The relevant checkpoint modules were exercised in CI run `45463102601`.
- `im-results/agent32-source-queue/` contains the q0 partition, source-drain, and source-coverage development. Its intended partition is the 129 slices `q_i (100*i) 100`, with the final slice naturally truncated to 20 input nodes.

The critical semantic distinction is that a finite checkpoint may leave both an active queue and held nodes. Both are obligations. A nonempty active queue is not a drained queue.

## Exact finite-checkpoint pilots

### Final chunk

`Agent5PackedChunk12800_20_1000000.v` records the existing final-20 checkpoint after 1,000,000 updates: 56 active, 0 held. `Agent5Last20Witness.v` provides short-run verdict proofs for those 56 active nodes. This is a finite checkpoint, not the terminal MAXT holdout list.

### First chunk

`q0-export/pilot-0-100-fuel-1000000.json` records the exact result for:

```
SearchQueue_upds decider (q_i 0 100) 1000000
```

Source revision: `ccz181078/busycoq@33209bc7dc282b38c8cd6be507bfc551fea56108`.

CI run `45522264094`, job `138896824472`, produced the exact packed checkpoint:
- 156 active, 1 held, 157 residuals total;
- no duplicate packed nodes;
- hole counts: 1→9, 2→3, 3→18, 4→23, 5→2, 6→5, 7→97;
- fresh-state counts: 3→16, 4→66, 5→55, 6→20;
- the single held node is one-hole;
- no table string in this chunk's residuals occurs in the historical 663-row snapshot.

The VM computation itself took 64.821 seconds. This supports the existing batch export's 180-second per-chunk timeout for this chunk; other chunks still need empirical confirmation.

## Export tooling

- `check-q0-export.cjs` parses packed queue values, checks the six-row table encoding, independently checks undefined-transition counts and fresh-state metadata, and writes a roster TSV plus JSON manifest. Its full mode expects exactly 129 chunks at offsets 0, 100, ..., 12800, requested size 100, and a consistent source/research revision.
- `.github/workflows/shared-rocq-root-proofs.yml` now runs the parser self-test and emits per-chunk Coq logs for `enumerate62-packed-batch`, making the exact values machine-readable through the Actions logs.
- Current batch run `45523811152` uses research revision `8350420137f3b1b45302be198e4cb2c9a2751d1a` and covers offsets 100 through 800 at fuel 1,000,000. It is the first eight-chunk batch and tests the workflow/parser integration.

## Native-computation caveat

The workflow target named `enumerate62-chunk-probe-native` is not currently native. The installed Debian Coq reports that native computation is disabled at configure time and falls back to `vm_compute`. The attempted MAXT probes for chunks 0–100 and 12800–12820 timed out under that fallback. These are not native-performance results. A genuinely native Coq build would require separate installation/configuration.

## Historical holdout snapshot

`resources/BB6_holdouts_663_2026-10-16.txt` contains 663 historical rows: 661 one-hole rows and two two-hole rows:

```
1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF
1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---
```

These are not assumed to belong to the current source-generated roster. The first 0–100 checkpoint has zero overlap with the historical snapshot, but full membership comparison must wait for the complete 129-chunk export.

## Next steps

1. Complete and inspect batch run `45523811152`.
2. If it passes, export the remaining 120 chunks in 15 eight-chunk batches at fuel 1,000,000, keeping a fixed research revision.
3. Parse all 129 exact active/held checkpoint values into `q0-export/q0-checkpoint-roster.tsv` and `q0-export/q0-checkpoint-manifest.json`.
4. Compare the complete roster with the historical 663 snapshot.
5. Work with Agent32 to discharge the finite residual obligations through the adaptive-plan coverage theorem. If the 1m residual roster is too large to certify directly, deepen only the difficult chunks rather than attempting another VM MAXT drain.

All computational exports and pilot data remain in `im-results/`; none is presented as an academically publishable result or as a solution to BB(6).
