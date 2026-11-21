# Agent 24 finite replay note: whole windows versus suffix closure

I ran the exact `highLevelNext` root recurrence from D(0,7) through source indices 33–10000 and scanned every entire target S-window `[k'+2,j'-2)` with both reset recognizers.

Both the full 263-state DFA and the source-derived 252-state DFA accepted all 9,968 target windows (D34–D10001); maximum first acceptance was at position 12. No finite-trace target window was accepted only by the source-derived DFA. For source index 33, target D34 has `x=57468, y=46704, S=67656, k'=6, j'=17`, length 7; both DFAs first accept after 4 symbols.

This is only finite evidence. It does **not** resolve the index-33 suffix-closure counterexample in `PhaseAutomaton.md`: a reset in the old word need not survive in an arbitrary output suffix. The diagnostic above scans the entire next target window. Keep the index-33 regression and all high-extension/whole-window obligations.

The source-derived product remains useful for its smaller 635/813 Moore quotients and its formal conditional reset lemma, not because it changes the observed 10k acceptance trace.
