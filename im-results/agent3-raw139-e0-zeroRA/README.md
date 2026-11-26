# Raw139 E0=0RA parent Cover

## Source-accepted result

The E0=0RA six-hole parent is the exact table

```lean
fromCodes [7,24,11,24,14,24,24,16,1,11,24,24]
```

under the repository convention `4*q + 2*w + right`. The 24-child partition and parent Cover at weighted bound **321,796** are source-accepted in CI run **45778885358**; the certified artifact is `raw139-e0-0ra-certified` (artifact ID 15100202529).

`Raw139E0ZeroRAMatch.lean` matches this parent exactly to normalized Raw139 row `(2, ⟨false,true,0⟩)`. `Raw139E0ZeroRAIntegrated.lean` then removes that row from the historical 67-table normalized list, proves the remaining count is **66**, and exposes the conditional `raw139_cover_after` interface. The integration is source-accepted in CI run **45797137615**. The initial attempt, run 45790610736, failed because `WeightedBound` was not opened from `BB6.Agent13BlankDelay`; commit `b8467d6d0d4b5cb70eda75170515b6ab5e9118ed` fixed the namespace, and the successful run rejects `sorryAx`/nonstandard proof shortcuts.

The 66-row interface is conditional, not a completed parent Cover: it still requires Covers for the 43 accepted sibling rows and all 66 residual tables at the target bound, together with the rowRC/rowRE continuation lifts and p7 Cover.

## Active Canonical64 integration

The historical normalized 67→66 list is distinct from the active Canonical64 Raw139 descendant list. Agent14's `Canonical64Raw139Subcover.lean` proves the E0=0RA table occurs exactly once in the active 80-leaf `remainingRaw139AfterFortyThree` list, lifts its 321,796 Cover to the champion score, and reduces that active list to **79**. This is a candidate conditional interface of 63 other Canonical64 Covers plus 79 Raw139 Covers = 142 obligations; it is not a global BB(6) proof.

The wrapper has not yet been source-accepted in its combined Canonical64 run. Agent6's 43-sibling consumer run **45793950237** was still in progress at the last check. Once it succeeds, dispatch `agent3-raw120-complete.yml` in `integrate-65` mode with:
- `raw139_subcover_run_id=45793950237`
- `raw139_e0_integrated_run_id=45797137615`

The existing workflow now also compiles Agent14's `Canonical64Raw139NormalizedCrosswalk.lean` probe (commit `d448e5bcc109c0b60f6cd6cd3297c42d5b60981a`) after the wrapper. It tests whether the 66 normalized residual tables refine active leaves and whether E0=0LC has exact/refinement membership. The probe is diagnostic and does not alter the 142-obligation count unless its output supports a formal subcover theorem.

## Scope

This result closes one explicit E0=0RA cylinder. It does not determine BB(6), prove a universal upper bound for the champion, or reduce the active Canonical64 obligation count until the combined wrapper is source-accepted. Keep the local 67→66 count separate from the active 80→79 count.
