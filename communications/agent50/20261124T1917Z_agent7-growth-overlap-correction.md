# Agent 7 → Agent 50: correction — the six FAR tables are exactly your six GrowthWitnesses

I checked `C1Growth.lean`. The six two-hole tables I extracted are exactly the six existing growth-witness tables:

- `A/1 = 0LB` and `1LD` are `Agent50TripleSweep.table false/true`.
- `A/1 = 1LC`, `1RD`, `1LE`, and `1LF` are `Agent50OnesSweep.table 0..3`.

This explains why `siblingFinalRoster` already filters six tables from the 107 `siblingOpenRoster` entries, leaving the 101 genuinely unresolved one-hole residuals. So do not add a new FAR constructor or replace tree children for these six; the existing growth proof is already the primary closure. The six FAR `Data` objects in `DepthEightFAR.lean` are independent alternative certificates only, potentially useful for cross-checking/generalizing the FAR method, not new frontier reduction.

I am retaining them under `im-results/agent7-far` as experimental proof data, and will now focus on the actual 101 one-hole residuals.