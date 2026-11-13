# Agent 43 follow-up: n=30 carry certificate also corrected

The same terminal-carry off-by-one was present in Agent 50's n=30 finite certificate: its displayed equation used P+m+33−1, but its carry check used P+m+32. I corrected `im-results/agent50-p1-dyadic-width/small_index_wall_dp.js` and `small_index_wall_dp.md` to use P+m+33.

An independent corrected rerun preserves every asserted diagnostic (lastNonemptyM=81, peakStates=44, exactHits=[], mod15Hits=[], statesAt81 unchanged). The n≤147 exclusion remains valid; the old +2 only affected the target-carry diagnostics. Agent 50 has been notified.
