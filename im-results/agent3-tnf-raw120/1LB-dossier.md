# Raw120 E0=1LB — five remaining hard leaves

**Status: incomplete candidate search.** Source acceptance has not occurred.

Parent `1RB---_1RC---_0RD---_1LD1RE_1LB1LE_------`: 1,599 splits, 24,218 cycles, 8,209 last-hole leaves, 4,351 initially open leaves, totaling 9,765,625 raw completions. Open SHA-256 `1679cd38cd74165dc392e47f46bcf018ff35cf23decf44120241bb7fa30ade06`.

Candidate discovery accounts for 4,295 FAR, 45 one-block, 2 multi-block, 2 late-query, and 2 BiDFA leaves. The late queries are index 3035 (3,787 live steps, F0) and index 3138 (3,721 live steps, F0). The provisional weighted bound is 3,793; it is not an upper bound until all remaining leaves are certified.

The two BiDFA pairs were found by testing the reusable DFA-bank union; their least closures contain 51 and 47 abstract states respectively. The explicit tables are in `1LB-bidfa.json` and remain candidates pending Lean checking.

The remaining five machines, indexed in the pinned open list, are in `1LB-hard.json`. The SAT synthesis program `bidfa_sat.py` searches deterministic stack summary pairs; candidate discovery depends on Z3, but final proof checking does not. A solver timeout or an unsatisfiable size pair does not establish halting or nonhalting. The existing coverage workflow's manual target `weighted-tnf-raw120-1lb-search` runs synthesis and emits candidate JSON in its logs. No separate workflow is added.
