# #429: right-four MidA boundary reduces to canonical Junc for every parameter

## Source-verified mathematical result

The original-source zipper for six-state machine
`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`
has the following exact **whole-tape** transitions for every `k : Nat`.
Write `A1(v) = z 0 (true :: (pairs01 (v+5) ++ ones 5)) true [false,true]`.

| Starting symbolic state | Canonical endpoint | Exact successful steps | Net head displacement |
| --- | --- | ---: | ---: |
| `A1(2*k)` | `junc 0 0 (4*k+22)` | `34*k+211` | `-(4*k+17)` |
| `A1(2*k+1)` | `junc 0 0 (4*k+28)` | `40*k+277` | `-(4*k+19)` |

Lean declarations `BB429W4Closure.even_boundary_to_canonical` and `odd_boundary_to_canonical` are in [`W4Closure.lean`](W4Closure.lean). They compose the new [`W4ScanE.lean`](W4ScanE.lean), the new [`W4JuncOne.lean`](W4JuncOne.lean), and existing source-certified macros. They check in the **actual repository source dependency graph** under Lean 4.36.0-rc2, with no `sorryAx`: [successful manual CI 42519846792](https://github.com/FlareZ123/bb6/actions/runs/42519846792), source revision `690e3f37e48ff7d53ce9e397163f7456cc3a1dd0`. The workflow is manual-only [`agent1-429-w4-scanE.yml`](../../.github/workflows/agent1-429-w4-scanE.yml).

This closes both parity branches of the formerly open **A/1 right-four terminal boundary**. The conclusion is conditional on its symbolic input. It does not classify the authentic blank-origin machine.

## Exact proof chain

1. The first 19 primitive moves carry `A1(v)` to `sourceScanE (v+4) (sourceSuffix 0)` at displacement `-3` (`boundary_to_sourceScanE_delta`). The theorem is definitionally checked by `rfl` from the original action table.
2. The existing `sourceScanE_finishC_even_delta` and `sourceScanE_finishC_odd_delta` split the `v` parity into `junc 2 (2*k+6) 1` and `junc 0 (2*k+7) 1`, respectively. This source-checked stage takes `18*k+109` or `18*k+85` moves, including the 19-step prefix.
3. For every `v≥1`, `junc 2 v 1` reaches `junc 0 0 (2*v+10)` in `8*v+54` moves with head displacement `-6` (`junc2_w1_to_junc0`). This uses the existing `juncPos_to_midA_delta` and `midApos_to_junc0_of_base` plus source-certified `midAaux_zero_base`.
4. For every `k≥0`, `junc 0 (2*k+7) 1` reaches `junc 0 0 (4*k+28)` in `22*k+192` moves with head displacement `-6` (`junc0_odd_w1_to_junc0`). This passes exactly through a 16-step `B/1 -> sourceScanE` macro, an odd `sourceScanE_e1_revisit_delta` return, a 20-step C/1-to-E/1 macro, and the existing all-parameter E/1 sweep and twelve-step tail.

The two primitive short macros in step four are directly checked by `rfl`; the unbounded sweeps are proved inductively by their source authors. All displacements refer to the physical head relative to the input's head. The original source action table is audited row-by-row in [`BB429SourceRows.lean`](../agent6-429-one-sided-excursion/BB429SourceRows.lean).

## Composition with the earlier MidA partial-sweep input

Agent32's previously certified [`midApos_zero_w4_boundary_delta`](../agent32-429-high2-prefix/MidAposBoundary.lean), [successful CI 42419998685](https://github.com/FlareZ123/bb6/actions/runs/42419998685), gives, for each `v`:

```lean
runWithDelta (4*v+35) (midApos 0 v 4)
 = some (A1(v), 3)
```

Consequently, by exact source-theorem composition, the complete **synthetic MidA right-four branch** has the following mathematical corollaries:

| Starting state | Canonical endpoint | Steps | Net displacement |
| --- | --- | ---: | ---: |
| `midApos 0 (2*k) 4` | `junc 0 0 (4*k+22)` | `42*k+246` | `-(4*k+14)` |
| `midApos 0 (2*k+1) 4` | `junc 0 0 (4*k+28)` | `48*k+316` | `-(4*k+16)` |

The two MidA compositions are paper corollaries of separately source-certified Lean theorems, while the A/1-to-canonical statements are additionally checked as single imported Lean declarations. The current expanded `MidAposBoundary.lean` includes unrelated later experimental lemmas with a **failed later source audit**; cite the successful earlier revision for its prefix theorem rather than treating its entire latest file as certified.

A finite independent raw-step simulator also checked the A/1-to-Junc formulas for sampled parameters; this is secondary evidence and cannot replace the all-parameter source proof.

## Remaining all-time obstruction

For the previously open right-four endpoint, the unresolved synthetic continuation now starts at the **canonical** states `junc 0 0 (4*k+22)` or `junc 0 0 (4*k+28)`. Existing full/partial Junc-cycle source lemmas can analyze those further, but their current forms do not establish a complete halt/nonhalt decision for the authentic blank orbit. In particular, the parameter `k` here is freely chosen and does not prove a given boundary actually occurs from blank tape. For the distinct right-five terminal, the A/0 boundary retains a separate unbounded suffix question; see the neighboring [high-2 dossier](../agent32-429-high2-prefix/README.md).

The source-verified [physical halting criterion](../agent32-429-raw-parent/README.md) is still that the authentic blank trajectory reaches a C/0 with marked right neighbor, equivalently B/001. Proving its actual reachability or impossibility remains essential to deciding #429. No BB(6) exact value, global upper bound, or new blank-run witness is claimed. Therefore this intermediate result belongs in `im-results/`, not `results/`.
