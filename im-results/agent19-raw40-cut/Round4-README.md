# Raw40: 0LA/1LB five-hole coverage candidate

Parent: `1RB0LA_1RC1LB_0RD---_1LD1LA_------_------`. The original canonical first-hole enumeration (1000-step cutoff) yields 374 residual leaves. FAR5 finds witnesses for 349; all other 25 have locally kernel-accepted unbounded pumping certificates. No enclosing Cover is claimed until the sharded audit finishes.

## Final difficult leaf 311

`1RB0LA_1RC1LB_0RD1RE_1LD1LA_1RA0RF_---0RB` has no FAR witness through six DFA states. A longer targeted parametric search finds the following exact family (zipper left includes the scanned cell):

`C(n) = (A, [], 0111000 (111111111111)^n 1110111)`.

Blank entry at step 57; for every n, exactly 224n+322 ordinary transitions take C(n) to C(n+1), without reading the unassigned F0 transition. This yields universal NeverHalts over compatible completions. Four right sweeps of 20 transitions per 12-bit block and four left sweeps of 36 transitions per block; fixed segments 12,15,43,20,52,25,61,36,58 sum to 322. Not a nested variable-count loop after all; the full macro required a larger symbolic search budget than the earlier generic search.

## Kernel acceptance

All 25 `Raw40Round4Pump.lean` theorems compiled with Lean 4.36.0-rc2 against accepted canonical77 artifact 14997966221 and exact Agent46AutoPump Git blob 9fb5e24599f4037123dc87d4e722f400eccabf6b; each printed only [propext, Quot.sound]. Regenerate from `python3 emit_autopump.py round4-pumps.jsonl BB6.Agent19Raw40.Round4`. All 25 machine strings match the indices in the unmodified canonical enumerator (blob edf5720193e89f861b3aa289273be396ea909efe). The enumeration's largest observed weighted halting score is 334 (333 primitive transitions then halt, delay 0). Enclosing canonical audit at WeightedBound 334 is in progress; 349 FAR witnesses are not yet counted as accepted coverage. No global roster decrement.
