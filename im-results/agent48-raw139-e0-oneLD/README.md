# Raw139 E0=1LD: exact candidate partition with the two difficult leaf proofs

For parent `[7,24,11,24,14,24,24,16,14,11,24,24]` the candidate weighted upper bound is **29,607,414**. This remains a parent certificate candidate pending source compilation, not a global BB(6) bound.

## Mathematical closure of the exceptional leaves

- [H1784](H1784.md), literal `[7,24,11,13,14,23,20,16,14,11,5,1]`: arbitrary-width binary counter overflow and a genuine 364-step entry yield all-completion nonhalting. Original-source Lean gate [45968302555](https://github.com/FlareZ123/bb6/actions/runs/45968302555) succeeded at `c5c5ef0f5ab24e43ecc73ecee4542944245ef50c`, artifact 15183777402. This closes the previously unresolved computational leaf.
- [H328](H328.md), literal `[7,24,11,21,14,5,0,16,14,11,17,5]`: 982-step entry, 1919 certified binary increments and 53,946 overflow steps yield exact first-hole time 29,607,408; weighted bound 29,607,414. Locally checked against original compiled semantic objects from artifact 15166454197. Fresh full-source parent audit will check the exact thirteen-module proof bundle.

## Exact graft and remaining gate

The saved 450-step, DFA-size-two replay partition has 19,813 splits, 272,735 cycles, 112,692 last-hole leaves, 52,684 FAR leaves and 17,589 open tables. One additional split at original open 9504 (time 717, slot 3) preserves all 24 ordinary moves; its 20 Block-FAR and four finite children are included. The complete **candidate** is 19,814 splits, 455,723 terminal leaves: 272,735 cycles, 112,801 finite last-hole traces (excluding H328), 52,684 FAR, 17,501 Block-FAR, H328 and H1784. The longest other late trace is 85,579.

The local reproduction with the exact replay and `prepare.py` checked the saved manifest hash and open-table order, every late first-hole pair, literal equality of both exceptional leaves, and all 24 children of the new split. Graft SHA-256 `58545e7a225c852bbac782ee268464b79a1fcc68746b80be24265ccec068b07a`; compact spec SHA-256 `f97d5ddd15b94d542cfaf1a7c3db7a45de063e901e88bfd22c62562b03bfb51b`.

The reused OneRA pipeline emits sparse Block-FAR proofs, packed long traces and the existing weighted-prefix checker. The exact H328 weighted leaf is substituted by literal table in the intermediate tree; it is never treated as a nonhalting theorem. The final export target is `BB6.Agent48Raw139E0OneLD.all_completions_weighted`. Manual workflow `agent48-raw139-e0-oneRA.yml`, target `oneLD`; prepare, twelve disjoint shards and final join must all pass. No global subtraction before source acceptance and exact current-roster membership.
