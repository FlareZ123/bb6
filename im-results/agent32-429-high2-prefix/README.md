# #429 high-2 C/B branch: source-connected partial closure

## Status

The high-2 C/B endpoint is now connected to the authentic six-state transition table by a universal Lean proof. The continuation from that endpoint to `midA2` is also source verified. The remaining `midApos(1,v,1)` to `Junc(0,0,2v+10)` suffix is still open.

This is an intermediate research result. It does not decide the blank-start orbit of #429 and does not contribute a BB(6) upper bound.

## Verified theorems

### 1. High-2 zipper continuation

[`High2Prefix.lean`](High2Prefix.lean) proves the exact `runWithDelta` composition from `high2SweepStart u` to `midA2 (2*u+4) 1`. A failed rewrite was repaired by normalizing the index `2*u+2 = 2*(u+1)` before applying `sourceScanE_finishC_even_midA_delta`.

- Lean CI: [42405659040](https://github.com/FlareZ123/bb6/actions/runs/42405659040)
- The workflow's fail-closed `sorryAx` check passed.

### 2. Physical C/B endpoint representation

[`High2PhysicalBridge.lean`](High2PhysicalBridge.lean) proves that the exact raw configuration emitted by Agent 1's `j_c_sweep u (2*u+2)` theorem is represented by `high2SweepStart u`. The representation checks the alternating painted segment, the six-cell setup fringe, the two right-side ones, the following `01`, and the blank right tail.

The same module composes the raw `j_c_sweep` prefix with the source-verified high-2 zipper macro. For every `u : Nat`, from the authentic J-chart configuration `J(u,2*u+2)` (state A, head 0, tape `jTape u (2*u+2)`) the original transition table reaches a configuration represented by `midA2 (2*u+4) 1` after exactly

```
4*u*u + 32*u + 132
```

primitive steps. The final head is `2*u+6`.

- Lean CI: [42407287630](https://github.com/FlareZ123/bb6/actions/runs/42407287630)
- The workflow compiled the original frontier and the physical bridge, printed theorem axioms, and passed its fail-closed `sorryAx` audit.

## Remaining suffix and empirical evidence

The endpoint `midA2 (2*u+4) 1` has the shape of `midApos 1 (2*u+4) 1`. The proposed remaining zipper theorem is

```
runWithDelta (6*v+48) (midApos 1 v 1)
  = some (junc 0 0 (2*v+10), -(2*v+8))
```

For `v=2*u+4`, this would cost `12*u+72` and return to `J(0,4*u+18)`. The resulting full raw return would have cost `4*u*u+44*u+204` and head offset `-(2*u+10)`.

This suffix is **not yet Lean proved**. Agent 1 independently simulated the complete raw branch for `u=0,...,20`, checking the translated J endpoint tape over its full finite support and blank margins. That is finite computational evidence only. Agent 32's auxiliary reduction proposal is:

```
midAaux(v,k) =
  z 0 (ones(2*v+1) ++ [false] ++ ones(6))
    true (tens(k) ++ [false,true])

runWithDelta 6 (midAaux(v,k))
  = some (midAaux(v-3,k+3), -6)       -- v >= 3

runWithDelta (6*v+4*k+36) (midAaux(v,k))
  = some (junc 0 0 (2*(v+k)+6), -(2*v+4))
```

The six-step recurrence and the three base cases `v=0,1,2` still need a kernel-checked proof. A request to Agent 6 asks for an independent proof or a precise blocker. See the relevant messages in `communications/agent6/`.

## Next work

1. Prove the `midAaux` six-step recurrence directly from the source transition table.
2. Prove the three base cases for arbitrary `k`, or derive a better finite phase decomposition.
3. Compose the suffix with `j_high2_to_midA_raw` and verify the exact full return to `J(0,4*u+18)`.
4. Integrate the high-2 branch into the complete #429 J-chart classification. The separate `w=2u` and `w=2u+1` C/B cases and the authentic blank-root entry remain unresolved.

## Reproducibility

- Transition table: `1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA`.
- Pinned Lean toolchain in CI: Lean 4.36.0-rc2.
- Source modules and exact theorem statements are in the two Lean files linked above.
- The CI workflow is `.github/workflows/agent32-429-raw-parent.yml`.
