> **Authentic-source verification update (Critic, 2026-11-03 17:38 UTC).** Manual workflow [41669051558](https://github.com/FlareZ123/bb6/actions/runs/41669051558), job [126032158499](https://github.com/FlareZ123/bb6/actions/runs/41669051558/job/126032158499), **succeeded** at 16:00 UTC. Its actual executed steps built the pinned original Cryptids acceleration, `S4UpstreamBridge.lean`, and the complete `S4RawTwoGates.lean` composition. The log reports `S4SourceBridge.original_machine_halts_iff_two_exceptional_gates` with exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. This upgrades the original-source *bridge/equivalence* from pending to verified. It **does not** decide whether either genuine blank-root exceptional sector is reachable, prove S4 nonhalting, or determine BB(6). Earlier local-only/pending status paragraphs below are historical and are superseded by this update; retain them as the development record.

## Source API fidelity correction

The initial candidate used `Function.iterate` as a term, which is absent in the documented Mathlib interface; the authentic notation `f^[n]` expands to `Nat.iterate`. A source audit corrected the adapter and independently retyped stand-in to `Nat.iterate`, preserving the theorem types and local Lean4.36 kernel check. The correction supersedes the initial hashes in commit history and is reflected in the current checksums below.

# S4 genuine-source interface candidate (2026-11-03)

**Status: locally typechecked against a faithful upstream-definition stand-in; authentic upstream import has NOT been compiled.** R004 / Agent 5. This is an intermediate bridge investigation, not a new decided six-state machine or a BB(6) bound.

## Scientific question

The eight original S4 intermediate modules in [Agent 5's S4 reduction](../agent5-s4-head/README.md) are proven against an independently copied, branch-for-branch version of Google DeepMind's published accelerated transition. The missing obligation is to connect *that* local map to the authentic source theorem that the original raw six-state machine halts iff the high-level accelerator halts.

The pinned source is [DeepMind Cryptids, commit c86f15861709b76042998c5211c7b2f83991621b](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean). Its definitions are `Stack.bumpHead`, `Stack.bumpHeadBy`, `transferHL`, `stepEpoch`, `highLevelNext`, and the root `highLevelStart = .C 3 [0]`. Its original theorem is `isHalt_iff_highLevel_acceleration`.

## Artifacts

- [S4UpstreamBridge.lean](S4UpstreamBridge.lean) contains a direct import of the unchanged DeepMind module, with no duplicated upstream definitions. It defines `unwrap` and proves `bump_eq`, `bumpBy_eq`, `transfer_eq`, the universally quantified `epoch_eq`, `run_eq`, and `halts_iff`. It then translates the exact published `CollatzHalts` iterator convention and composes the published `isHalt_iff_highLevel_acceleration` to state `original_machine_halts_iff_model`:

  `IsHalt source.target ↔ ∃ n, S4.run n (3,[0]) = none`

  The file is a **candidate proof for original-source compilation**, not an original-source-checked result. SHA-256 of UTF-8 source: `779fcefe0e81fde9e7b6d0f725ccad144d3eccbbc1911ad6eb6e7a0254bb02ab` (5042 bytes).
- [S4UpstreamStandInTest.lean.xz.b64](S4UpstreamStandInTest.lean.xz.b64) preserves a separate Lean source test that imports the same original Agent5 `S4Phase` and copies the exact pinned DeepMind definitions into the same qualified names. Its **bridge proof body is identical to S4UpstreamBridge.lean**. The stand-in uses the original Mathlib orientation for `Nat.iterate`, with `Function.iterate_succ_apply'` proved rather than assumed, and replaces real `BusyBeaver.IsHalt` and the published raw-machine equivalence with a trivial model-level proposition, because its purpose is checking the *adapter's* type- and inductive-proof structure without the upstream dependencies. Stand-in decoded SHA-256 `cc70ae74ff767264c0ebfbb140af8162bf3196db3d67df93476f1d34ecee7cb3` (7470 bytes); Base64 wraps XZ bytes.

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

The prior shared GitHub Actions pre-step outage was resolved on 2026-11-03 at 15:55 UTC, confirmed by executed diagnostic [run 41668916380](https://github.com/FlareZ123/bb6/actions/runs/41668916380). The already-pinned authentic upstream check was submitted as [manual S4 run 41669051558](https://github.com/FlareZ123/bb6/actions/runs/41669051558), and as of 15:57 UTC its initial original-source build was underway. **This report has not yet inspected a completed source-specific proof step.** Do not grade the source bridge as authentic-source certified until that job actually compiles both the bridge and the full two-gate theorem; if compilation fails, record its exact error and repair the minimum necessary source.

**Mathematical scope:** Successful original-source checking would authenticate the existing S4 one-list reduction from the genuine blank root, but the deeper-tail halting gate remains unclassified. Even a completed S4 decision would be one rooted machine decision; no universal BB(6) upper bound or exact BB(6) value follows from this interface alone.
