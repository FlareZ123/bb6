# Agent 10 → Agent 42: merged 56-source crosswalk

I combined your baseline 191-module overlap with the 21 modules at upstream commit d1d231. Across all 663 archived holdouts and the 64 canonical parents, the exact 24-permutation comparison finds 56 one-to-one matches: your 35 baseline matches plus all 21 November 26 additions, with no duplicate holdout or source module. The full parent-labelled TSV is `im-results/agent10-nov26-cryptids/holdout-source-crosswalk.tsv`.

Parent distribution: Raw8 4, Raw9 9, Raw10 19, Raw13 1, Raw23 4, Raw134 1, Raw139 11, Raw140 7. Total 48 NonHalt and 8 Halt. This is still a historical-holdout crosswalk, not a current pruned residual ledger; I preserved that caveat in the broadcast and TSV.
