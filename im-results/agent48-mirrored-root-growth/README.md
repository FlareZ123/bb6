# Corrected #490 mirrored-root growth macro

**Status: intermediate research.** The root trajectory and macro were reproduced by a source-transcribed persistent-list interpreter. A local Lean model proves the 76-step outer-stack identity for every suffix. The exact pinned-original-source theorem is prepared for the existing manual Lean workflow; until that workflow succeeds, do not describe the macro as source-certified. The finite blank-root prefix is also not yet a Lean theorem.

## Root-reachable candidate state

Pinned upstream project: google-deepmind/cryptids commit
3647718b5df22e1a61462dec0376bd204526285a.

Exact #490 module:
BusyBeaver/BB6/Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean
(blob SHA f0bc716f48f69ffff474c8094c3254eaf7681acb).

The #490 wrapper transports the #85 closed pair-stack system using
ClosedStackSystem.mirror. The root replay uses the actual mirrored successor
swap(step85(swap(state))); do not substitute the synthetic #85 seed or the
old D_n(c) / H-phase route.

At outer macro index 1,153,484, the persistent-list replay gives a #490
configuration in mode DR with left length 182,119 and right length 14.
Its left stack begins

    [1] ++ B ++ T

where

    B = [0,2,0,0,0,2,0,0,0,16,0,0]

and its right stack is

    R0 = [0,1,0,0,0,0,0,0,0,0,1,0,0,0].

The concrete replay has length(T)=182106. Checkpoints at 100,000,
250,000, 500,000, 750,000, 1,000,000 and 1,153,484 match the
previously reported left-stack lengths 15,781; 39,465; 78,937; 118,411;
157,883; and 182,119. The checked-in fast_root_stack_sim.js remains the
reference simulator; the local replay used an independent persistent-list
reimplementation of its source-transcribed transition clauses.

## Exact candidate macro

For every finite suffix T, the 76-successor outer-stack identity is

    DR(L=[1] ++ B ++ T, R=R0)
      --76 outer successors-->
    DR(L=[1] ++ B ++ B ++ T, R=R0).

The right stack is unchanged, the left stack grows by 12 entries, and no
token-normalizer branch occurs. Seven explicit suffix regressions passed,
including empty, zero, one, mixed short, and large-entry suffixes. More
importantly, RootMirroredGrowthMacroModel.lean proves the corresponding
outer-rule identity for arbitrary T in the local Lean kernel.

This is a different macro from the old #85 synthetic DR/G/B right-insertion
macro and from the standalone H-phase CR macro. Its raw cost was derived
independently from the actual source branch cases in the 76-step mirrored
trace; it was not transferred from either earlier candidate.

| Underlying #85 source branch | Count | Cost each | Subtotal |
|---|---:|---:|---:|
| DR, left head 0 / positive right head | 8 | 4 | 32 |
| DR, positive left and right heads | 3 | 3 | 9 |
| CR, left head 0 | 13 | 2 | 26 |
| CR, left prefix 1,0 | 8 | 5 | 40 |
| CR, left prefix 1,empty | 1 | 6 | 6 |
| EL, right head 0 | 16 | 2 | 32 |
| EL, positive right head | 12 | 1 | 12 |
| DL, right head at least 2 | 4 | 4 | 16 |
| DR, empty left tail | 1 | 1 | 1 |
| DL, right head 0 | 8 | 6 | 48 |
| CR, left prefix 1,1 | 2 | 16 | 32 |
| **Total** | **76** |  | **254** |

No DR right-head-zero or DL right-head-one token branch appears in this
macro. The local Lean model represents those token branches as unavailable;
the successful 76-step reduction therefore certifies their absence in the
model. The exact source theorem below is the decisive check against the
pinned original machine.

## Formal artifacts

- RootMirroredGrowthMacroModel.lean: Lean 4.36.0-rc2 local model of the
  outer stack clauses. root_growth_76_pairs proves the suffix-parametric
  identity for arbitrary pair suffixes; its printed axiom profile is
  [propext]. The explicit 76-entry cost-vector sum theorem is axiom-free.
  This is a reduced source-transcribed model, not the original machine proof.
- RootMirroredGrowthMacro.append.lean: source theorem to append inside the
  exact #490 module. It uses the public closedStackSystem.evalStackCfg
  field and execute 254, followed by an axiom print.
- .github/workflows/agent32-hphase-growth-macro.yml is repurposed as a
  manual-only source check for this mirrored-root theorem. It still pins the
  exact upstream commit and toolchain. The older H-phase append file remains
  preserved but is not part of this run.

## What is and is not established

Established computationally: the corrected mirrored root replay reaches the
stated stack prefix at 1,153,484 outer successors; the 76-step local
reimplementation returns to the same DR mode and fixed right stack while
inserting B; seven suffix tests pass; the independently counted branch
costs sum to 254.

Kernel-checked locally: the reduced outer-rule model proves the
suffix-parametric 76-step identity. This is not yet a theorem about the
original target.

Still open: compile the exact execute 254 theorem against the pinned
original #490 module and audit its transitive axioms; source-certify the
finite blank-root prefix from init [] to this macro seed; then compose the
macro with that prefix. Only after both source obligations pass would this
give a genuine nonhalting proof for the #490 blank-start machine. It does
not determine BB(6) by itself.
