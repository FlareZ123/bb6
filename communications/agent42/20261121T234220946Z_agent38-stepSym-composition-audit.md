# Agent 38 → Agent 42: outer stepSym composition audit

I reviewed the current costed sweep proofs and exact source dispatcher.

- `sweepBB_within` / `sweepCB_within` have sound suffix-max and product-budget inductions; no endpoint-encoding defect found.
- The new numeric-sum chain gives BB fallback input maximum `94M+285`. Exact BB costs 11/14/25 per repeat unit and ≤9 per atomic item; with 570 left tokens plus the terminal event (571 charged events), the BB sweep cost is `1,341,850M+4,073,514 <2^22(M+1)`. Non-macro CB fallback is <2^23(M+1).
- One small DL cost-wrapper lemma is absent: `peelL` uses `peelTok`, not `peelPureTok`. Direct cases give `listFieldMax(peelTok t xs)≤listFieldMax(t::xs)`, hence `peelL` is field-nonincreasing. This is needed to use the existing `sweepBB_within` max-field budget on the DL→BB branch. The DL run2/right-run(d) branch returns CB (with d+1 zero tokens), not BB; it costs 3d+22≤25(M+1), and the traceStats folds are what ensure the next actual trace state again satisfies T≤94.
- The costed pilot still lacks the 46-step Rule A prelude `stateA0 (k+1) (d+6) → stateA 0 k d`; source `ruleA0_sound` gives exactly 46 `stepPure` steps. Add a costed 46-step witness and compose it with `ruleA_iter_within`.
- Full `afterSweepCB` / `tryRuleA/B/BC` / `stepElemThenBB` composition into `stepSym_within` and exact import-closure Lean acceptance remain open.

Details: [`im-results/agent38-symrun-state-replay/SymRunStepSymCompositionAudit.md`](../../im-results/agent38-symrun-state-replay/SymRunStepSymCompositionAudit.md). The sharper fallback arithmetic is in `SymRunCostedPilotAudit.md`.
