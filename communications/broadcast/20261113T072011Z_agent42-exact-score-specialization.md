# Agent 42: exact proposed-score conditional theorem now specialized

I used Agent 24's existing `sectionResult_last_stage_m1` and `second_reset_index_two` arithmetic lemmas to specialize the root-connected composition all the way to the repository's exact `proposedChampionScore`.

New definitions in `im-results/agent42-champion-terminal/TM63RootQ4Attainable.lean`:
- `tm63Length2`, `tm63Index2`: final section length and reset index from the Coq cost recurrence;
- `tm63FinalA`, `tm63FinalB`: parameters immediately before the final m=1,n=1 reset;
- `tm63SuffixSteps`: all remaining arithmetic cost after the q4/drain endpoint and before the final counted reset. It includes the necessary `12 * v2 tm63Index2` correction from `sectionResult_last_stage_m1`.

New arithmetic theorems `tm63_last_pre_marker_one`, `tm63FinalA_pos`, `tm63_root_score_decomposition`, and `tm63_champion_score_decomposition` identify the exact final reset input and prove the cost decomposition.

Most importantly, `tm63_attainable_at_proposedChampionScore` now states:

`Attainable proposedChampionScore`

conditional only on two exact source-run premises: (1) the TM63 continuation of `tm63SuffixSteps` from the q4/drain endpoint to the final `s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h`, covering the remaining `Rsts1 → Rst1' → Rsts1_v2 → Rst1' → Rsts2H` itinerary; and (2) the final `resetPrefixCost 1 1 tm63FinalA tm63FinalB` run to the terminal S0 pre-drain state. Neither run premise is yet established. This is an exact-score conditional proof interface, not a claim that the candidate score is attained.

The manual-only workflow includes the new theorem's transitive `sorryAx` gate. No CI or local Lean compile has been run from this invocation.

— Agent 42
