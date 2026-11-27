# Three-hole extension of Raw13 #1093

Parent: `1RB1LD1RC---1LA1RE1LF0LA---0RD1LC---` (15,625 literal completions, including all halt choices). Source-accepted conditional exact weighted score 134 (CI 45936411385); this equals the source-accepted *conditional* two-hole threshold (CI 45936148751). The new tree uses that two-hole certificate once and extends it to every B1 choice.

New mathematical leaf:
`1RB1LD1RC1RF1LA1RE1LF0LA---0RD1LC0RF`, sole hole E0. In state A, let the nearest-first left and right words be (1011) and ((01)^{6n+4}1). The blank seed reaches this family with n=0 at step 68. Its exact return sends n to n+1 at positive cost 144n+229. The supplied JSON trace consists of six arbitrary-tail sweep transfers of a 12-cell block (costs 36,12,36,12,36,12) interleaved with 229 fixed steps. It is not an extrapolation from a finite simulation; the existing Lean symbolic checker verifies the trace for all n.

The other new hard leaf `1RB1LD1RC1LB1LA1RE1LF0LA0RB0RD1LC---` has a 5-state FAR witness (left DFA 0123224322). The rest of the tree has 17 split nodes (with implicit halt branches), 186 translated side cycles, 157 last-hole queries, 46 bank FAR witnesses and the one previously proved 2-hole certificate. The maximum sparse-weighted finite bound outside the old cylinder is 123. Candidate census: 1215 halting literal completions, 14410 nonhalting completions; total 15625. The witness of 134 steps in the old cylinder remains compatible.

The `coupled3` source target generates the one sweep fixture, checks the entire new tree against exact repo semantics, and proves the exact threshold conditional only on the already published E0=1LA theorem. The independent upstream source transport is not yet integrated. The conditional local source check passed in CI 45936411385; the source bridge is still pending. Do not count this as an unconditional kernel-closed parent until the bridge succeeds.
