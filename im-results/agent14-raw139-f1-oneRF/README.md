# Raw139 F/1=1RF — complete weighted cylinder closure

**Original-semantics local Lean kernel accepted.** Parent table `[7,24,11,24,14,21,3,16,12,11,24,23]`; theorem `BB6.Agent14F1OneRF.all_completions_weighted` establishes `WeightedBound 5423` for every compatible completion. Axioms: propext, Classical.choice, Quot.sound.

The 11 splits produce 254 leaves: 136 translated cycles, 65 last-hole, 21 FAR, 29 affine growth, and 3 recursive carry proofs. All leaves closed. Initial 600-step scan had 37 open leaves; two last-hole computations (5417 and 1208), one cycle, and two size-4 FAR checks reduce these to 32 nonhalting leaves.

The source archive includes `WordShift.lean` (generalized conjugacy for arbitrary word repetitions), `FastQuery.lean` (exact zipper-to-knownRun bridge for long last-hole computations), `RunCarry.lean` (shared recursive carry invariant), the symbolic proof generator, and compact recipes. The generated proof breaks long affine recurrences into independently checked segments and checks each finite audit node separately to reduce kernel memory.

Reproduce with `bash reproduce.sh` from repository root (script path `im-results/agent14-raw139-f1-oneRF/reproduce.sh`), Lean 4.36.0-rc2. The local proof used verified original .olean dependencies from Agent48's successful artifact 15021380200 (run 45611897213, pinned commit c512623e68b633e28fc140370abee778cfaf0939), ZIP SHA256 910e843066c3bbf1ddb21d2b798c850cb671e66b743f4c91d750c6be723bc570. All 57 dependency hashes and compiler hash matched the manifest. Independent clean CI and exact canonical roster integration remain pending; no global BB(6) upper bound is claimed.

Independent full source audit passed on 2026-11-25: [run 45723873034](https://github.com/FlareZ123/bb6/actions/runs/45723873034), artifact 15072628795, `raw139-f1-oneRF-certified`. This independently checks the exact parent bound 5423. Global roster integration remains separate.
