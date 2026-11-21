# F424 SymRun costed-pilot and fallback audit

**Date:** 2026-11-21T23:30:02.968Z  
**Auditor:** Agent 38  
**Pinned source:** `google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a`  
**Status:** source-level review; exact imported-source Lean compilation remains pending.

## Outer sweep proof review

I reviewed the current `SymRunCostedStepPilot.lean` proofs of `sweepBB_within` and `sweepCB_within`, including the endpoint encodings and product-budget lemmas. No induction or budget defect was found.

- `sweepBB` consumes only the left stack. Its recursive calls use suffixes of the original left stack, so `pilotListFieldMax L1 ≤ pilotListFieldMax L`. The costs are 8/3 for run-0/run-1, at most 9 for the terminal `stepElemBB`, and exactly 11k/14p/25m for the three repeat sweeps. The `eatB1/eatB2/eatB12R` transformations affect the right stack only; `encSymR_eat*` gives the required exact endpoint equality. The 50-per-token product budget is conservative and valid.
- `sweepCB` consumes only the right stack. Its recursive calls use suffixes of the original right stack, so the right-side maximum is monotone. Costs are 21 for the run-0/run-1 pair, 3 for run-1, and exactly 21k/24p/45m for the repeat sweeps. The `eatB1/eatC2/eatC12` transformations affect the left stack only; `encSymL_eat*` gives the required endpoint equality. `pilot_budget_cons2` overcharges one token in the two-token branch, but safely. The 50-per-token budget is conservative and valid.
- `enc_eatFuel` correctly handles both same-kind counter merges (via `repBlock_add`) and literal-block matches (via `stripPrefixSym_some`); the wrapper lemmas are the right semantic bridge.
- The `stepElemBB_within9` uniform terminal bound is correct for all BB item branches and is independent of numeric fields.

## Stronger fallback bound from the numeric-field sum

Agent 44's current `SymRunTraceStats.lean` adds a useful direct field bound:

`sweepCB_num_sum_le_94M282` and `sweepCB_stateFieldMax_le_94M282` prove that after the CB sweep the maximum field is at most `94M+282`. The proof uses `eatFuel_num_sum_le`: every matched literal block contains at least one unit of run length, so moving it into a repeat counter does not increase total numeric-field sum; each `bumpSymL` contributes at most 3, and there are at most 94 calls.

For a BB-producing fallback, `stepElemCB_BB_num_sum_le` adds at most 3, giving
`cb_fallback_bb_input_field_max_le_94M285`. Thus the entire BB-sweep input field maximum is at most `94M+285`, conditional on the 94-token premise and the fallback mode being BB. This subsumes the older separate `94M+376` counter-sum / `M+94` bump estimates for bounding the input maximum.

A sharper BB-sweep time bound follows directly from the exact F424 cost table:
- each repeat token costs at most `25q` (the BB coefficients are 11, 14, 25);
- each non-repeat token costs at most 9 by `stepElemBB_within9`;
- each repeat parameter `q` is at most the BB-sweep input field maximum `94M+285`;
- the BB sweep receives at most 570 left tokens, and the recursive definition can make one additional terminal `stepElemBB` call; charge at most 571 events.

Therefore its primitive cost is at most
`571 * (25 * (94M + 285) + 9) = 1,341,850M + 4,073,514`,
which is strictly below `2^22 * (M+1)` for every natural M. This is an arithmetic consequence of the existing exact branch costs and field/token bounds; it is not yet packaged as a Lean theorem. The current generic `sweepBB_within` theorem uses coefficient 50, so a dedicated coefficient-25 version would make the improvement explicit in Lean.

Combining this with the existing outer CB-sweep bound `<2^13(M+1)` and the one fallback `stepElemCB` cost `≤25(M+1)`, the non-macro fallback path is below `2^23(M+1)`. The macro path still dominates the stated `2^39(M+1)^2` whole-`stepSym` estimate.

## Remaining cost-composition gaps

The current pilot contains `stepPure_within`, `stepPure_iter_within`, `sweepBB_within`, `sweepCB_within`, and costed Rule A/B/C iteration lemmas. It does not yet provide the complete `afterSweepCB` / `tryRuleA` / `tryRuleBC` / `stepSym` dispatcher composition.

One concrete missing Rule A component: upstream `ruleA0_sound` uses 46 `stepPure` iterations from `stateA0 (k+1) (d+6)` to `stateA 0 k d`, but the costed pilot currently contains `ruleA_step_within` and `ruleA_iter_within` only. Add a 46-step `ruleA0_within` using `iterStep_stepPure_within_eq 46` and the same definitional endpoint equality, then compose it with `ruleA_iter_within`. The source arithmetic gives total Rule A calls `46+66n_A`, with `n_A≤M).

No exact imported-source compile was performed in this invocation: local shell calls returned tool-level ClientErrors. Agent 44's source-equivalent preflight is useful but is not exact import-closure acceptance. No BB(6) solution or machine classification is claimed.
