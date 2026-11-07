# #429 high-2 C/B branch: exact raw return to the Junc family

## Status

The high-2 C/B branch is now source-verified from the synthetic J-chart input through a complete return to the Junc family. For every `u : Nat`, the original six-state transition table takes

```
J(u, 2*u+2)
```

to a configuration represented by

```
junc 0 0 (4*u+18)
```

in exactly `4*u*u + 44*u + 204` primitive steps. The final head displacement from the J-chart starting head is `-(2*u+10)`.

This is an intermediate branch-closure result. It does not establish that the authentic blank-tape orbit reaches `J(u,2*u+2)`, and it does not decide #429 or BB(6).

## Verified theorems

### 1. High-2 zipper continuation

[`High2Prefix.lean`](High2Prefix.lean) proves the exact `runWithDelta` composition from `high2SweepStart u` to `midA2 (2*u+4) 1`. The index normalization `2*u+2 = 2*(u+1)` is performed before applying `sourceScanE_finishC_even_midA_delta`.

- Lean CI: [42405659040](https://github.com/FlareZ123/bb6/actions/runs/42405659040).

### 2. Physical C/B endpoint representation

[`High2PhysicalBridge.lean`](High2PhysicalBridge.lean) proves that the exact raw configuration emitted by Agent 1's `j_c_sweep u (2*u+2)` theorem is represented by `high2SweepStart u`. The representation checks the alternating painted segment, the six-cell setup fringe, the two right-side ones, the following `01`, and the blank right tail.

The module composes the raw `j_c_sweep` prefix with the source-verified high-2 zipper macro. From the original transition table and the synthetic J-chart configuration `J(u,2*u+2)` (state A, head 0, tape `jTape u (2*u+2)`), the raw machine reaches `midA2 (2*u+4) 1` after exactly

```
4*u*u + 32*u + 132
```

primitive steps. The final head is `2*u+6`.

- Lean CI: [42407287630](https://github.com/FlareZ123/bb6/actions/runs/42407287630).

### 3. Universal zero-base MidA suffix

[`High2Tail.lean`](High2Tail.lean) repairs and source-verifies the six-step `midApos` reduction, the two-step `midAaux` reduction, and the composition theorem parameterized by a zero-base family.

[`High2TailBase.lean`](High2TailBase.lean) proves the exact boundary family, for every `k : Nat`:

```lean
runWithDelta (4*k+36) (midAaux 0 k)
  = some (junc 0 0 (2*k+6), -4)
```

The proof uses four finite phases:

1. `2*k+4` steps reach A/0 with left `ones (2*k+8)`, right `01`, and displacement `+2*k`. Four A/F steps normalize the fringe, then `k` A/01 pairs consume `tens k`.
2. Two A/0 steps and a fixed eight-step C/1 segment reach E/1 with left `ones (2*k+10)`, right `101`, and additional displacement `+2`.
3. E/1 sweeps left across the `2*k+10` ones, transferring them to the right, with displacement `-(2*k+10)`.
4. A fixed twelve-step tail consumes four leading ones and leaves the exact Junc tape, with displacement `+4`.

The total is `4*k+36` primitive steps and displacement `-4`.

The same file derives the full two-parameter closure:

```lean
runWithDelta (6*v+4*k+36) (midAaux v k)
  = some (junc 0 0 (2*(v+k)+6), -(2*v+4))
```

### 4. Complete physical high-2 return

[`High2Return.lean`](High2Return.lean) identifies `midA2 (2*u+4) 1` with the positive `midApos` family, lifts its exact zipper suffix through the raw-source representation theorem, and composes it with the physical C/B prefix.

The suffix costs `12*u+72` steps and displaces the head by `-(4*u+16)`. The complete raw theorem is:

```lean
j_high2_to_junc_raw (u : Nat) :
  ∃ c',
    BB6Coverage.run target429 (4*u*u+44*u+204)
      {state:=A, head:=0, tape:=jTape u (2*u+2)} = some c' ∧
    Represents (junc 0 0 (4*u+18)) c' ∧
    c'.head = -(2*u+10)
```

- Full source CI: [42413147930](https://github.com/FlareZ123/bb6/actions/runs/42413147930).
- Pinned source revision: `2a5f188b80512e69cf40a20c170cea88af8c8041`.
- Follow-on raw crossing CI: [42413538308](https://github.com/FlareZ123/bb6/actions/runs/42413538308), pinned revision `560640f3b34aeb49c82e006aebd07585230444cd`.
- The final theorem's transitive axiom audit is `[propext, Classical.choice, Quot.sound]`. The supporting zipper theorems use `[propext, Quot.sound]`. No audited high-2 theorem depends on `sorryAx`.

### 5. Exact endpoint and raw rightward crossing

The high-2 return endpoint is `junc 0 0 (4*u+18)`, with head displacement `-(2*u+10)`. Set

```
n     = juncTerminalN 0 (4*u+18)
spent = juncCycleSpent n 0
rem   = 4*u+18-spent
```

The source-verified `juncCycle_crossing_shape` theorem gives two exact endpoint cases.

1. **Small remainder:** if `rem ≤ 4`, the further run takes exactly `juncCycleTimeTotal n 0` steps, displaces the head by `spent`, and ends at `junc (juncCycleU n 0) 0 rem`.
2. **Partial sweep:** if `rem ≥ 5`, put `N = rem/2-1`. The further run takes exactly `juncCycleTimeTotal n 0 + juncPosMidTime N 0` steps, displaces the head by `spent+2*N`, and ends at `midApos (juncCycleU n 0-N) (2*(N-1)) (rem-2*(N-1))`. The final right parameter is 4 when `rem` is even and 5 when `rem` is odd.

[`High2Return.lean`](High2Return.lean) lifts these exact alternatives through the raw-source representation theorem. The theorem `j_high2_crossing_shape_raw` proves that every synthetic high-2 J-chart input has a finite raw-machine continuation with the stated endpoint and with final head strictly greater than `2*u+3` relative to the original J-chart head. The weaker head-crossing corollary is `j_high2_crosses_origin_raw`.

- Exact endpoint and raw crossing CI: [42414260489](https://github.com/FlareZ123/bb6/actions/runs/42414260489).
- Pinned source revision: `72fa2df0c311b8bbe5bd4530206e3ccf5bc27125`.
- The named high-2 endpoint and crossing theorem audits pass with no `sorryAx`.



### 6. Raw lift for finite halting suffixes

The physical bridge now also contains `BB429DeltaPhysicalBridge.source_runWithDelta_none_rep`. If a zipper state `z` represents a raw configuration `c` and `runWithDelta n z = none`, then the exact raw six-state machine run also satisfies `BB6Coverage.run target429 n c = none`.

The proof is by induction on the source run. Successful first steps use `sim_one_delta`; a source first-step halt is transferred to the raw transition table using `action_matches_target) and the representation invariant. This is a general halting-lift lemma, independent of the high-2 endpoint theorem.

- Source CI: [42415667222](https://github.com/FlareZ123/bb6/actions/runs/42415667222).
- The theorem's targeted axiom audit passes with no `sorryAx`.

The high-2 endpoint alternatives have not yet been classified as halting or nonhalting. The new lemma supplies the raw-machine side once a finite zipper-level halting suffix is proved.


## Remaining #429 questions

The high-2 case `w=2*u+2` now returns to `junc 0 0 (4*u+18)`, and a further source-verified Junc excursion crosses the original J-chart head to a position strictly greater than `2*u+3`. The separate C/B cases `w=2*u` and `w=2*u+1` remain open. The J-chart outer cases are source proved: `w=2*u-1` halts, and `w>=2*u+3` returns to the J family. The crossing theorem leaves the final zipper abstract, so a useful next step is to expose its exact endpoint alternatives and compose those alternatives with the outer J-chart classification.

The authentic blank-root entry remains a separate question. The high-2 theorem starts from the synthetic state `J(u,2*u+2)`. The global #429 decision still requires determining whether the genuine blank orbit visits B with tape `001` at and immediately right of its head.

## Reproducibility

- Transition table: `1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA`.
- Lean toolchain in CI: Lean 4.36.0-rc2.
- The manual source workflow is `.github/workflows/agent32-429-raw-parent.yml`.
- Run [42413147930](https://github.com/FlareZ123/bb6/actions/runs/42413147930) compiles the complete dependency chain, checks the named high-2 theorem audits, and passes.
