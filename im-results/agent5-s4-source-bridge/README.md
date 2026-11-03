# S4 genuine-source interface candidate (2026-11-03)

**Status: locally typechecked against a faithful upstream-definition stand-in; authentic upstream import has NOT been compiled.** R004 / Agent 5. This is an intermediate bridge investigation, not a new decided six-state machine or a BB(6) bound.

## Scientific question

The eight original S4 intermediate modules in [Agent 5's S4 reduction](../agent5-s4-head/README.md) are proven against an independently copied, branch-for-branch version of Google DeepMind's published accelerated transition. The missing obligation is to connect *that* local map to the authentic source theorem that the original raw six-state machine halts iff the high-level accelerator halts.

The pinned source is [DeepMind Cryptids, commit c86f15861709b76042998c5211c7b2f83991621b](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean). Its definitions are `Stack.bumpHead`, `Stack.bumpHeadBy`, `transferHL`, `stepEpoch`, `highLevelNext`, and the root `highLevelStart = .C 3 [0]`. Its original theorem is `isHalt_iff_highLevel_acceleration`.

## Artifacts

- [S4UpstreamBridge.lean](S4UpstreamBridge.lean) contains a direct import of the unchanged DeepMind module, with no duplicated upstream definitions. It defines `unwrap` and proves `bump_eq`, `bumpBy_eq`, `transfer_eq`, the universally quantified `epoch_eq`, `run_eq`, and `halts_iff`. It then translates the exact published `CollatzHalts` iterator convention and composes the published `isHalt_iff_highLevel_acceleration` to state `original_machine_halts_iff_model`:

  `IsHalt source.target ↔ ∃ n, S4.run n (3,[0]) = none`

  The file is a **candidate proof for original-source compilation**, not an original-source-checked result. SHA-256 of UTF-8 source: `ec7e962b3f5cde2084168af3af39499cc70729bc483d348b8bd31f27c8531130` (5042 bytes).
- [S4UpstreamStandInTest.lean.xz.b64](S4UpstreamStandInTest.lean.xz.b64) preserves a separate Lean source test that imports the same original Agent5 `S4Phase` and copies the exact pinned DeepMind definitions into the same qualified names. Its **bridge proof body is identical to S4UpstreamBridge.lean**. The stand-in replaces real `BusyBeaver.IsHalt` and the published raw-machine equivalence with a trivial model-level proposition, because its purpose is checking the *adapter's* type- and inductive-proof structure without the upstream dependencies. Stand-in decoded SHA-256 `9a7c7de8e1cbd00783f9d75801b91aca0c7a87b27879d3cfe96ae3eb7f607eb8` (7341 bytes); Base64 wraps XZ bytes.

## Verification performed

Using the supplied Lean 4.36.0-rc2 locally, Agent5's original compressed `S4Phase.lean` (decoded SHA-256 `6f63cee92357a425db24131de7f43547503c06e982df2abc844e1d5c30ea293f`) compiled to its .olean. The stand-in compiled against it. `#print axioms` for `epoch_eq`, `highLevelNext_eq`, `halts_iff`, `sourceRun_eq_iter`, `original_highLevel_halts_iff_model` and `original_machine_halts_iff_model` all returned only `[propext, Quot.sound]`; no `sorry` or `sorryAx`. One unused-simp-argument lint was harmless.

This **does not certify** the authentic source-import file: a definition copied into a stand-in is not itself the original constant, and the stand-in's raw-machine endpoint is merely an assumption-free toy replacement. Although the adapter's statements and proof scripts coincide with the test body, the real upstream elaborator may reveal imports, namespaces, recursion-elaboration, theorem-signature, or unfolding mismatches.


## Full-root two-gate composition candidate (added 15:42 UTC)

[S4RawTwoGates.lean](S4RawTwoGates.lean) imports this adapter and the existing Agent5 `S4Hazard` theorem. By a direct transitivity step, its `original_machine_halts_iff_two_exceptional_gates` would establish, against the **actual six-state machine**, the exact all-time equivalence

```text
IsHalt original_S4 ↔
  ∃ n s, (n % 8 = 4 ∨ n % 8 = 7) ∧
    S4.reducedRun (9 + n) [42,12,8,5] = some s ∧
    S4.reduced s = none
```

This formalizes precisely the *residual unknown* without confusing a necessary gateway with a settled nonhalting proof. The composition file has **not** been freshly source-compiled; the underlying `S4Hazard` was earlier reported locally kernel-checked, and the imported original bridge is still source-CI pending.

The pre-existing manual [Agent7 S4 source workflow](../../.github/workflows/agent7-s4-original.yml) has been extended with SHA-256 verification of the original eight compressed Lean modules, the direct original-source import adapter, and this final two-gate composition. **No run has been dispatched under the ongoing no-step GitHub Actions incident.** Only a successful source-matched job (including actual executed steps) can upgrade the current evidence grade.

## Reproduction and next discriminator

First decode the original `S4Phase.lean.xz.b64` and the stand-in with Python's built-in Base64/XZ decoders, preserving original filenames, and check their byte SHA-256 values. Compile `S4Phase` as an importable module and then compile the stand-in with Lean 4.36.0-rc2. To test the actual obligation, install the pinned Cryptids project including its matching Mathlib dependencies, make `S4Phase` importable in that project, and compile `S4UpstreamBridge.lean` **without editing the source module**. Audit the printed axioms and check the root `IsHalt` theorem against the actual constant. Record exact full-file hashes, import/toolchain versions and CI logs.

As of 2026-11-03, the shared Actions incident describes jobs failing before any steps execute; no new original-source import claim is justified until a real source-matched successful run. Do not generate repeated dispatches under the ongoing incident. The next target is a single authorized source-matched check when runners recover. If compilation fails, preserve the first exact error and make the smallest source-level repair.

**Mathematical scope:** Successful original-source checking would authenticate the existing S4 one-list reduction from the genuine blank root, but the deeper-tail halting gate remains unclassified. Even a completed S4 decision would be one rooted machine decision; no universal BB(6) upper bound or exact BB(6) value follows from this interface alone.
