# R001: original BusyCoq proof-source audit of four removed BB(6) rooted machines

Agent 12, 2026-11-03. Intermediate provenance result, no independent Rocq recompilation.

Original source: ccz181078/busycoq, branch BB6 commit 33209bc7dc282b38c8cd6be507bfc551fea56108.

| October 24 root | Exact RLE | Source statement | Reported outcome |
| --- | --- | --- | --- |
| 146 | 1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD | verify/Sk1Machines_v2.v, TM25.nonhalt: ~halts tm c0 | nonhalting, original formal proof source |
| 247 | 1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0RA--- | verify/SOMDCv10.v, TM4.halt: halts tm c0 | halting, original formal proof source |
| 411 | 1RB0RC_1LC1RC_1LD0RB_1LA0LE_1LF---_1LC1RA | verify/Sk1Machines_v2.v, TM26.nonhalt for reflected table | nonhalting, original formal proof source plus reflection |
| 531 | 1RB1LC_1RC0LE_1RD1RF_1LE0LB_1RF1LB_0RA--- | verify/Sk1Machines_v2.v, TM23.nonhalt: ~halts tm c0 | nonhalting, original formal proof source |

Source links:
- https://github.com/ccz181078/busycoq/blob/33209bc7dc282b38c8cd6be507bfc551fea56108/verify/Sk1Machines_v2.v
- https://github.com/ccz181078/busycoq/blob/33209bc7dc282b38c8cd6be507bfc551fea56108/verify/SOMDCv10.v

Sk1Machines_v2.v has literal table TM25 for root146 and TM23 for root531. TM26 contains left-right reflection of root411. Explicit root411 to root146 state relabeling A->D, B->A, C->B, D->C, E->E, F->F and simultaneous L/R flip. Root411 blank-A maps to root146 blank-D, while TM25's blank-A theorem is a separate root. The paper trail is careful to distinguish these initial states. A local Lean 4.36.0-rc2 direct theorem checks all twelve edges and all finite raw-step executions; its final theorem 'BB6.Agent12.RootPair.blank_halting_equiv' used only standard axioms. This is a standalone reflection bridge, not recompilation of the upstream Rocq nonhalting proofs.

Root119 1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE has an original-source halting equivalence in verify/Eqv_v2.v module TM2153, linking to the auxiliary rooted machine 1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD. No independent decision was found for either: root119 remains unknown here. Root109 was explicitly assigned to a different investigator.

Scientific caveat: source declarations with proof scripts are primary evidence of a claimed formal decision. We have not yet independently compiled source and dependencies or audited native_check_eq and kernel assumptions. They must not be called independently Rocq-certified here. The dated roster deletion was never itself a proof. This research is provenance integration, previously published mathematics, not a new BB(6) value, BB(6) upper bound, or novel root theorem.

Next: compile original unmodified Sk1Machines_v2.v and SOMDCv10.v with associated dependencies and print assumptions of TM25.nonhalt, TM26.nonhalt, TM23.nonhalt, TM4.halt; independently check the exact root411 reflection. Trace the auxiliary TM2153 root as a separate potential status lead.

## Reproducible independent audit of root119's equivalence

The [source's own README](https://github.com/ccz181078/busycoq/blob/33209bc7dc282b38c8cd6be507bfc551fea56108/README.md) warns explicitly: halting equivalences can eliminate duplicate holdouts **even when no member of their equivalence class is decided**. Thus a disappearance from the roster may be a representative change alone.

The standalone Node.js CJS single-file regression [test-root119-eqv.cjs](test-root119-eqv.cjs) independently simulates the two original blank roots in *raw* primitive steps and checks the full 12 transition table under state permutation `BCDEAF`. It verifies no halt before either checkpoint, and the **entire** tapes relative to the respective heads agree at the exact finite coalescence:
- Auxiliary `1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD`: **315075** steps; state C, head -467.
- Deleted #119: **337226** steps; state D, head -466.
- Each has **280** ones, same relative tape positions between offsets **+1 and +512**, and states agree after `C -> D` under `BCDEAF`.

The exact match supports the provenance of the already-written original `Eqv_v2.TM2153.eqv`, but by itself supplies **no** nonhalting/halting decision and therefore no new upper bound for BB(6). Never mark row119 decided merely because a finite equivalence check passes.

The direct source-table reflection to original upstream `Sk1Machines_v2.TM26.tm`, including an all-time blank-A equivalence theorem, is also independently checked in the extended Lean module's `original_tm26_blank_halting_equiv`. It closes the source-code bridge for removed row411 while still depending on upstream kernel verification for the actual nonhalting theorem.

## Reproducible source-build attempt

A reusable, manual-only [Rocq original-source verification workflow](../../.github/workflows/shared-rocq-root-proofs.yml) was added with an exact upstream pin, `sk1`/`somdc` targets, and final theorem `Print Assumptions` audit. It specifically avoids the environment's unsupported `-native-compiler yes` precompile mode (which caused `Unbound module Nativevalues` in an earlier independent Agent46 attempt), allowing kernel VM conversion fallback. Its initial `sk1` run **41578398072** started 2026-11-03 04:29 UTC; record its *actual* final outcome before upgrading any source proof to independent compilation.
