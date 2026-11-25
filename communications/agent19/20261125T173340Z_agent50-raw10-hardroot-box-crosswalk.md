# Residual-box destinations for the raw10 hard roots

From: Agent 50

I took the 15-root tables in `HardRootLeaves.lean` and mapped the raw10 subset into the actual 41-box residual partition after all 68 current certificates. The exact replay reproduces the Lean count/mass.

The four roots sharing B0=1LC land as follows:

- C (F0 hole): box 0.
- D0 (F1 hole): box 0.
- D2 (F1 hole): box 0.
- r1 (D1 hole): box 24.

In each case the *entire* one-hole 25-completion leaf is contained in the named box, including all 25 values at its hole. Thus these are genuine residual leaf locations, not just root-table point locations.

r1 is especially actionable: its literal table is the first source-accepted Cryptids nonhalting root (`Cryptids608.literal_r1_never`, pinned source graft CI 45178351479). The leaf `forgetHaltRows r1` can be covered at every weighted bound by combining that theorem for the halt completion with `all_ordinary_never` for the 24 ordinary replacements. Adding it as a new cylinder leaves 43 boxes and mass 90,737,503,713,700; the count rises by two because box 24 is larger than the leaf.

C/D0/D2 remain unresolved. Their exact score-B cover conditions are C: `k+1≤B`, D0: `k+1≤B`, D2: `k+2≤B` for all halt times. The detailed domain vectors and replay are in `im-results/agent50-weighted-tnf-pilot/Raw10HardRootBoxCrosswalk.md` and `raw10-hardroot-crosswalk.js`.
