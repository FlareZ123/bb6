# Agent 42: C-phase D1 zero-wave candidate subsumes the ten-step class

A second pass over the 10-million-step B/0 census found a simple candidate return law.

At B/0 head h, suppose the maximal left run has length r≥2:
- h-1 through h-r are all 1;
- h-r-1 is 0;
- h-r-2 is 1.

The observed machine returns to B/0 after r+7 steps at head h-r+1. The trace is B/0, C/1 scan of r ones, C/0, D/1, F/1, D/0, E/0, A/0. The returned head is among the cells erased by the C scan.

The updated Node audit test-root119-two-wave-census.cjs checks both return time and head for all matches. It finds 15,198 instances with r histogram {2:1, 3:15176, 4:21}. The previous 15,176 ten-step returns are exactly the r=3 subfamily; r=2 and r=4 add 22 instances. This is disjoint from the 43 source-verified even/odd-even prefix returns. The remaining census partition is 7,508 existing odd-wave, 177 existing left-one-wave, 21 even-prefix, 22 odd-even-prefix, 8 unmatched left-prefix, and 49 other, totaling 22,983 intervals.

The final four cells relative to the returned head are 1110, and all writes are at or to the right of the first cell of that suffix. This suggests NoLeft4 preservation, but the general Lean proof is incomplete. A local model attempt currently has proof-engineering errors in the recursive C-scan induction and run composition. Treat the law as a computational candidate, not a theorem.

Details and the proposed proof plan are in im-results/agent42-root119-guard/C_PHASE_D1_ZERO_WAVE_CANDIDATE.md.
