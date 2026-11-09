# All-parameter #429 right-two exceptional Junc census

**Machine:** `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`.
All states and tape words here refer to the exact original two-symbol source zipper; `C/0` means a configuration whose state is C and scanned symbol is 0. `runCount` counts C/0 configurations at executed primitive instruction starts, excluding the endpoint.

## New complete right-two macro law

For **every** `k : Nat`:

| Exact input | Executed primitive steps | Exact endpoint | C/0 instruction starts |
| --- | ---: | --- | ---: |
| `junc 0 (2*k) 2` | `38*k+204` | `junc 0 0 (4*k+18)` | **2** |
| `junc 0 (2*k+1) 2` | `44*k+266` | `junc 0 0 (4*k+24)` | **3** |

These are the statements `junc0_w2_all_even_count` and `junc0_w2_all_odd_count` in [W2JuncFullCount.lean](W2JuncFullCount.lean). The formerly unclassified (v=0,1) cases have kernel-decided base proofs (`runCount 204` and `runCount 266`). For all larger parameters the proof factors the 19-step A/1 boundary, complete source S_E crossing, C/1 finishing sweep, and previously certified Junc(0,v,1) continuation. In the even branch a new independent exact all-parameter Junc(2,v,1) one-C/0 count closes the last gap.

This is a genuinely complete **source-chart branch** result, including intermediate primitive instructions and exact counts. It remains a conditional chart result: no theorem currently shows that authentic blank-origin #429 remains in the combined chart forever. These identities do not establish BB(6), its upper bound, or #429's blank-origin halting behavior.

## Novel reusable source lemmas

[W2MidAauxCount.lean](W2MidAauxCount.lean) establishes a new full C/0 census for the residual A/F boundary:

- `midAaux_zero_count k`: exactly one C/0 in the `4*k+36`-step return.
- `midAaux_all_count v k`: exactly one C/0 after arbitrary additional A/F pair reductions, uniform in both unbounded parameters.
- `midApos_w1_count v`: exactly one C/0 in every positive-middle `MidA` right-one return.

[W2CZeroEvents.lean](W2CZeroEvents.lean) strengthens these results to locate the unique A/F C/0 with an **entirely empty right half-tape**, guarded against earlier C/0 starts. In particular, `junc2_w1_gate_safe v` reaches C/0 at exactly `6*v+22` source instructions with left stack `10 1^(2*v+14)`, right stack empty, uniformly for `v>=1`. The independent full-return count certifies uniqueness.

The new `finishC_ScanE_safe` statement verifies that the unbounded C/1-to-A and A/1,F/1 phase has zero C/0 starts. `boundary_to_scanE_count` shows exactly one C/0 in its initial fixed 19-step A/1 boundary. They combine with previously established safe E/1 scanning and the Agent1 right-one C/0 census.

## Evidence and reproducibility

**Source Lean 4.36.0-rc2 verification:** the complete [W2MidAauxCount.lean](W2MidAauxCount.lean) theorem suite passed the unchanged-source [CI audit 42579371054](https://github.com/FlareZ123/bb6/actions/runs/42579371054), which printed only standard axioms and no `sorryAx`.

**Composite audit pending:** [W2JuncFullCount.lean](W2JuncFullCount.lean) and [W2CZeroEvents.lean](W2CZeroEvents.lean) passed local Lean 4.36.0-rc2 preflight against an exactly transcribed source zipper and the declared interfaces of already repository-certified dependencies; this local harness represented those imported theorems by signatures, so it is an interface/type check, not a complete independent original-source certificate. Attempts at the manual source CI [42580169904](https://github.com/FlareZ123/bb6/actions/runs/42580169904) and [42580496563](https://github.com/FlareZ123/bb6/actions/runs/42580496563) failed **before any Lean source was compiled**: the public release server returned HTTP 504 while installing Lean. Run the existing [manual source workflow](../../.github/workflows/agent1-429-w4-scanE.yml) again once the external release download recovers. Its first dependency, W2MidAauxCount, already passed an earlier source run.

## Next step

Combine the new all-parameter right-two return with the previously certified right-one and ordinary branches and prove a **blank-origin inductive chart/history invariant** on actual physical tapes. The absence of fatal C/01 in an isolated return follows from the successful source return, but ruling it out over the entire authentic infinite trajectory requires controlling all chart entries and their earlier physical head histories.
