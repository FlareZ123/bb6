# Sheep 1458 full-tree Lean acceptance

**Status: accepted as an exact five-family non-reachability theorem.** The complete dependency closure for `SheepPower1458.noEvenReachFiveFamilies` compiled successfully with Lean 4.36.0-rc2 in [GitHub Actions run 45293408209](https://github.com/FlareZ123/bb6/actions/runs/45293408209).

## Exact compiler evidence

- Workflow: `.github/workflows/agent14-sheep-power1458-tree-preflight.yml` (existing manual workflow; no new workflow was created).
- Run: [45293408209](https://github.com/FlareZ123/bb6/actions/runs/45293408209), job `138107652784`, successful.
- Pinned branch: `agent14/sheep1458-preflight-20261123`.
- Exact source commit: `f79ea4c7a6799611626b9d5904e969f227b452cd`.
- Lean: `4.36.0-rc2`, commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`.
- The job restored the SHA-checked Agent16 source archive and compiled the full dependency sequence through `SheepPower1458TreeProof.lean`.

The exported theorem reports:

```text
'SheepPower1458.noEvenReachFiveFamilies'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` appears in this profile. The key source and arithmetic dependencies also compiled; among the printed profiles, `lowRow_no_generic_progression`, `lowRow_no_generic`, and `affine_node_hidden_bound_from_cert` depend only on `[propext, Quot.sound]`, while the source wrappers and final theorem use the standard `Classical.choice` axiom as well. The run reached and completed the final `#print axioms noEvenReachFiveFamilies`.

## Compiled dependency closure

The workflow compiled, in dependency order:

- Agent16 source modules: `SheepEven`, `EvenEdge`, `OddPrefix`, `EvenReach`, `BlankEven`.
- Source/inverse modules: `SheepEvenInverseAlgebra`, `SheepEvenSourceAlgebra`, `SheepEvenReachInverse`, `SheepOddGap`.
- Shared arithmetic modules: `SheepGenericHigh`, `ResidueGap`, `GenericHighNoParent`.
- The full 1458 chain: `SheepPower1458Core`, `SheepPower1458Rows`, `SheepPower1458All`, `SheepPower1458RootGate`, `SheepPower1458High`, `SheepPower1458Target`, `SheepPower1458AffineBounds`, `SheepPower1458SourceIntegration`, `SheepPower1458LowRows`, `SheepPower1458RootEdgeTable`, `SheepPower1458LowRowTable`, and `SheepPower1458TreeProof`.

The final theorem is the conjunction of the five progression-family exclusions. The 75 base residues across the five periods correspond to 93 classes when the `h=7,a=4` family is lifted to the common period `T₂=3T₄`.

## Corrections relative to the earlier failed run

The earlier run [45281313128](https://github.com/FlareZ123/bb6/actions/runs/45281313128), on commit `87d07431eb0daa68548945d25ef25f551c1269f8`, failed in the then-current `TreeProof` source. Its concrete diagnostics included:

- the special-source equation was passed before the required algebraic normalization;
- the node-10 bound was not exposed in the arithmetic form required by `omega`;
- the inferred `treeParentClosed` application left its implicit endpoints unresolved;
- `cases hk` was run after simplification had already closed an empty-key goal;
- the `EvenReach` module was not imported directly into the final proof file.

The current proof has the normalized special equation, explicit `hsmall'` and typed parent-closure hypotheses, guarded empty-key cases, and an explicit `import EvenReach`. The successful run above verifies the resulting complete source closure.

## Local runtime boundary

The prescribed local bootstrap was attempted once in this invocation. `container.exec` returned platform `ClientError` before the shell command executed; a trivial Python runtime call also returned `ClientError`. No extraction or local Lean process occurred, and no archive byte count was obtained. This is a tool-boundary failure, not a Lean diagnostic and not evidence that the uploaded archive is corrupt.

The documented fallback was therefore used: one targeted run of the existing manual full-tree workflow, pinned to the exact source commit. Do not repeat the local bootstrap in this invocation or dispatch another unchanged workflow.

## Scope and remaining work

The accepted theorem proves non-reachability in the exact `SheepEven.EvenReach` relation for the five listed infinite progression families. The separate machine-source equivalence `BB6.Agent16.SheepEvenSource.raw_halts_iff_even_power` was accepted earlier in [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547); `EvenSourceBridge.lean` was not part of this run's compile closure. Together, the two accepted results rule out halting witnesses whose exponent lies in these five families. They do not exclude all other possible halting exponents, decide the Sheep machine, or determine BB(6).

Keep this result in `im-results/`. Freeze the 93-family list and avoid further period/row expansion. The next valuable mathematical step is a broader invariant or a complete decision of the residual even-return orbit.
