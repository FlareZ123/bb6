# #429: all-parameter right-four MidA boundary continuation

## Exact theorem and scope

For the standard #429 two-symbol six-state Turing machine
`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`,
the original transition-table zipper `runWithDelta` satisfies, for every `v : Nat`:

```lean
runWithDelta 19
  (z 0 (true :: (pairs01 (v+5) ++ ones 5)) true [false,true])
  = some (sourceScanE (v+4) (sourceSuffix 0), -3)
```

This is the exact A/1 endpoint of Agent32's already-verified `midApos_zero_w4_boundary_delta`. It is a whole-tape equality, not a finite-window or sampled-run extrapolation. It connects the previously unclassified right-four endpoint directly to the source S_E family after 19 primitive transitions.

Composing with Agent6's source-checked `sourceScanE_finishC_even_delta` and `sourceScanE_finishC_odd_delta` gives the following **all-parameter exact Junc returns**:

| `v` | Starting A/1 boundary | Endpoint | Steps | Net head displacement |
| --- | --- | --- | ---: | ---: |
| `2*k` | `z 0 (true :: pairs01 (2*k+5) ++ ones 5) true [false,true]` | `junc 2 (2*k+6) 1` | `18*k+109` | `-(4*k+11)` |
| `2*k+1` | `z 0 (true :: pairs01 (2*k+6) ++ ones 5) true [false,true]` | `junc 0 (2*k+7) 1` | `18*k+85` | `-(4*k+13)` |

All three propositions are formalized in [`W4ScanE.lean`](W4ScanE.lean). They import **the existing original repository source modules** and compile without `sorryAx`. [Manual CI 42518949437](https://github.com/FlareZ123/bb6/actions/runs/42518949437) passed on commit `12cec4378f8a55834421dc36abe0a2d16902696c`. The workflow is [`agent1-429-w4-scanE.yml`](../../.github/workflows/agent1-429-w4-scanE.yml), manual dispatch only. Local Lean 4.36.0-rc2 also checked the pure 19-step source macro against the identical explicit machine action and zipper definitions without axioms. An independent raw-tape Python simulator checked both final configurations and absolute head positions for `v=0..39`; the finite screen is a cross-check rather than the theorem's basis.

## Link to the earlier right-four partial-sweep endpoint

Agent32 previously source-certified [`midApos_zero_w4_boundary_delta`](../agent32-429-high2-prefix/MidAposBoundary.lean), on [CI 42419998685](https://github.com/FlareZ123/bb6/actions/runs/42419998685):

```lean
runWithDelta (4*v+35) (midApos 0 v 4)
  = some (z 0 (true :: (pairs01 (v+5) ++ ones 5)) true [false,true], 3)
```

Combining that certified predecessor with our new all-parameter boundary theorem yields the following *direct mathematical corollaries*, not yet packaged as separate imported Lean declarations:

- `midApos 0 (2*k) 4` reaches `junc 2 (2*k+6) 1` in `26*k+144` steps, with head displacement `-(4*k+8)`.
- `midApos 0 (2*k+1) 4` reaches `junc 0 (2*k+7) 1` in `26*k+124` steps, with head displacement `-(4*k+10)`.

Both results hold for every natural `k` by exact composition of two certified source theorems and addition of integer displacements. They eliminate the unspecified A/1 boundary from the prior description of the w=4 branch, reducing it to two explicit Junc right-budget-one families.

## Remaining mathematical problem

The attained Junc states are synthetic conditional configurations; no all-time blank-root reachability argument is established. They have right budget exactly one, so existing full `juncPos_next_delta` (requiring budget at least two) does not apply directly. The even-sector `junc 2 v 1` has a source-verified next step to `midApos 1 v 1`, which is covered by the existing high-2 `midApos` tail. The odd-sector `junc 0 v 1` reaches an explicit A/0 right-budget boundary by `junc0_to_B_delta`. Closing this second boundary uniformly, or proving a genuine blank-root invariant, would materially strengthen the #429 account.

The theorem does **not** decide #429 or BB(6), change a universal Busy Beaver bound, or establish a new blank-orbit witness. It belongs in `im-results/` pending a stronger machine-level result.
