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

## Exact C/0 clock and terminal frontier geometry

The signed-displacement refinement [W2FinalDelta.lean](W2FinalDelta.lean) proves a stronger statement than the C/0 counting certificate: **every right-two Junc return ends with its head exactly 10 positions left of its starting location**, independent of the unbounded parameter and its parity. Its `physical_even_w2_delta` and `physical_odd_w2_delta` statements transport the -10 displacement to every genuine entire-tape original-machine configuration represented by the starting chart, using the established zipper-to-physical bridge. The rightmost prescribed marked position nevertheless grows monotonically across this macro. Relative to the initial original head, its new position lies **6 cells beyond the old marker for even v**, and **10 cells beyond for odd v**. The corresponding marker-location equalities are `even_w2_frontier_extension` and `odd_w2_frontier_extension`.

The exact right-two event clocks, measured in original primitive steps from Junc entry, are:

| Initial middle parameter | First C/0 | Second C/0 | Third C/0 |
| --- | ---: | ---: | ---: |
| `v=2k` | `4k+35` | `34k+164` | none |
| `v=2k+1` | `4k+37` | `26k+137` | `40k+220` |

Every listed event has an **entirely blank right half-tape**; the full-return `runCount` proves there are no additional C/0 visits inside that macro. The first visit and its no-earlier-C/0 guard are source-certified by [Agent 30's ZeroTwoGate](../agent30-429-positive-safe/ZeroTwoGate.lean); the uniform even second visit and one prior C/0 are formalized by [W2EvenEvents.lean](W2EvenEvents.lean), while the odd second and third source `runWithDelta` visits, their absolute head offsets, and finite v=1 base are formalized in [W2OddEvents.lean](W2OddEvents.lean).

In each parity the displayed later gates move the head three cells to the right of the preceding gate. The exact head shifts at the even second gate are `4k+10` and at the odd second and third gates are `4k+13` and `4k+16`. The initial rightmost marked-cell offsets are `4k+5` and `4k+7`. These formulae make the gate-to-marker geometry explicit for possible root-history induction, although current source proofs have not yet established a universal all-prefix head-max certificate for the full right-two macro.

**Verification note:** the new event and -10 displacement source files were proved in local Lean preflight against the original zipper and declared interfaces of existing source-certified lemmas. Their full unmodified-repository CI audit is still a separate obligation, and this section should be promoted to verified original-source status only after it succeeds.
