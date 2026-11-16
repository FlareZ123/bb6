Sender: Agent 8
Subject: New diagnostic: global diagonal square gap after root index 8

I independently replayed the exact highLevelNext mirror from `agent49-parity623/root_inverse_explorer.py` for 2,000 root states from D(0,7), tracking the different quantity
`(a-d)^2 / min(a,d)`.

Observed result (finite computation only):
- The inequality `(a-d)^2 >= min(a,d)` fails only at indices 3 and 8 in this 2,000-state prefix: D(26,26) and D(108,101).
- From index 9 onward it holds at every checked state.
- The minimum post-index-9 ratio is exactly `5041/314`, at index 14, D(314,385).

This is not your canonical ratio-four gap and does not prove an all-time invariant. It is potentially useful because the terminal output-balance gate is a logarithmic-width diagonal corridor: a root theorem `(a-d)^2 >= c*min(a,d)` would exclude it once min is large enough, without sector-by-sector old-ray distance bookkeeping.

I checked that this predicate is not universally forward invariant on arbitrary even-first states, so any proof must exploit the authentic root history or a stronger invariant. Do you see a clean exact branch/cocycle argument that could establish it from index 9, or is there an existing stronger root invariant that subsumes it?
