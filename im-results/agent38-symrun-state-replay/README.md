# Checkpointed SymRunEngine state replay: F424 and F412

**Status: reproducible computational evidence.** This replay independently translates the upstream `SymRunEngine` state transition `stepSym` into JavaScript, executes every macro transition, and compares the resulting state against every source checkpoint. It does not calculate primitive TM time and is not a Lean theorem.

## Source and reproduction

Pinned upstream source:

- Repository: `google-deepmind/cryptids`
- Commit: `3647718b5df22e1a61462dec0376bd204526285a`
- Engine: `BusyBeaver/Calculi/HaltShared.lean`
- Machine certificates: the F424 and F412 files under `BusyBeaver/BB6/Halt/`

The dependency-free script `symrun_state_replay.cjs` exports a function accepting a source-fetch callback. Its Node usage is documented in the script header. It parses `initSymCyc3` and the literal `symChkN` states from the two source files, replays `stepSym`, and checks exact equality at every checkpoint.

All checkpoint comparisons pass:

| Machine | `stepSym` transitions | Source checkpoints matched | First HALT state |
|---|---:|---:|---:|
| F424 | 70,511 | 18 / 18 | 70,511 |
| F412 | 21,383 | 6 / 6 | 21,383 |

The final replayed symbolic state is abstract HALT in both cases; the source theorem applies one separate concrete primitive step_DL_zero_halt transition afterward. At the pinned Cryptids revision, repository searches for `initSymCyc3` and `symChk4096` return exactly these two BB6/Halt machine modules; `stepSym4096` appears in those two modules and the shared engine. Thus this replay covers both machine modules using this SymRun checkpoint signature. Both exact machine codes also occur in im-results/agent42-cryptids-upstream-191-overlap/upstream-exact-overlap.tsv as IsHalt rows, currently marked not established by the ledger and not curated; a certified primitive-time bound would add two concrete below-champion classifications.

## Maximum encoded-state sizes over the complete replay

The script measures every state after every `stepSym` transition, not only the checkpoints. Per-chunk maxima, checkpoint endpoint maxima, and the exact peak step are preserved in [checkpoint-maxima.json](checkpoint-maxima.json).

| Metric | F424 maximum | Bits | F412 maximum | Bits |
|---|---:|---:|---:|---:|
| Largest individual run/repeat field | 12,464,561,897,144,001,482,331,935,594,779,263,804,489,570,179,353,031,112,091,137 | 203 | 412,597,277,036,535,862,786 | 69 |
| StepSym transition attaining max field | 70,298 | — | 21,275 | — |
| Sum of repeat counters | 12,464,561,897,144,001,482,331,935,594,779,263,804,489,570,179,353,031,112,085,238 | — | 412,597,277,036,535,860,912 | — |
| Decoded tape length (including repeated blocks) | 31,161,404,742,860,003,705,829,838,986,948,159,511,223,925,448,382,577,780,216,103 | 205 | 1,031,493,192,591,339,653,257 | 70 |
| Number of symbolic tokens | 94 | — | 78 | — |
| Largest `prependZeroSym` expansion | 12 | — | 10 | — |

The decoded tape-length calculation expands each `repB1` as 2 items, each `rep2` as 3 items, and each `rep12` as 5 items, without physically allocating those repetitions.

## What this establishes—and what it does not

Established computationally:

1. The translated `stepSym` transition reproduces every literal upstream checkpoint for both machines.
2. Both replayed symbolic traces reach the source's final HALT checkpoint at the stated macro counts.
3. The complete trajectories have the recorded finite maxima for run fields, repeat counters, decoded tape length, and symbolic-token count.

Not established:

- a primitive TM-step count for any `stepSym` macro;
- a complete primitive halting time for F424 or F412;
- a comparison of either complete halting time with the BB(6) champion.

The measured 203-bit / 205-bit F424 bounds and 69-bit / 70-bit F412 bounds support the stronger, still-unformalized trace-specific route in [SymRunPrimitiveBound.md](SymRunPrimitiveBound.md). That route targets F424 < 2^463 and F412 < 2^193, conditional on the cost-indexed soundness theorem, the intermediate-state max-field/token-count folds, and the prefix bound. A second route is now documented in [SymRunCoarseWeightPotential.md](SymRunCoarseWeightPotential.md): the combined potential W = 1 + token count + numeric-field sum now targets the much looser but still below-champion bounds F424 < 2^1,552,000 and F412 < 2^471,000, without the per-checkpoint maximum-field folds. Reusing the pilot's existing BB left-length bounds sharpens the generic target to W(stepSym(s)) <= 2^10(W(s)+1). The route still requires the generic sweepBB/dispatcher weight lemmas, Rule B field-sum arithmetic, and a complete costed afterSweepCB wrapper. Neither route is a certified classification; both require exact-source Lean compilation and axiom auditing.


**Range-proof warning:** do not infer an intermediate-state bound from checkpoint endpoints alone. The replay records maxFieldInChunk separately from maxFieldAtCheckpoint, and the former is often larger. For example, F424's first chunk peaks at 419,581 while its endpoint field maximum is 349,284; the final chunk peaks at 12,464,561,897,144,001,482,331,935,594,779,263,804,489,570,179,353,031,112,091,137 while the endpoint is smaller. The Lean proof must fold over every intermediate state.
