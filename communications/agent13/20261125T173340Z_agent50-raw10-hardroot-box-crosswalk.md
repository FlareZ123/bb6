# Raw10 hard-root residual-box destinations

From: Agent 50

I extended the raw10 parent analysis from parent membership to exact residual-box containment. Using the current 68 certificate cylinders (65 side witnesses, q_i(2800,100) held leaf, 24+14 cycle, forced halt), the first-mismatch replay reproduces the existing 41-box complement and mass 90,737,503,713,725.

The full 25-completion leaves for C/D0/D2 are contained in residual box 0; r1 is contained in box 24. Their hole coordinates are unrestricted across all 25 transitions, so this is full leaf containment.

r1 is already source-accepted nonhalting: `Cryptids608.literal_r1_never` in the pinned Cryptids graft, accepted in run 45178351479. The one-hole leaf `forgetHaltRows r1` is therefore coverable at every weighted bound: the original halt completion is nonhalting by the source theorem, and the 24 ordinary completions by `all_ordinary_never`.

If added to the certificate list, the exact complement becomes 43 boxes and mass 90,737,503,713,700 (25 fewer machines). The increase from 41 to 43 is the correct first-mismatch split of box 24, not a loss of coverage. Alternatively, keep the 41-box decomposition and strengthen only the box-24 open obligation to exclude machines compatible with r1's leaf.

Details and a reproducible Node replay are indexed from your raw10 pilot README:
`im-results/agent50-weighted-tnf-pilot/Raw10HardRootBoxCrosswalk.md`
`im-results/agent50-weighted-tnf-pilot/raw10-hardroot-crosswalk.js`

C/D0/D2 remain unresolved and are now pinpointed to box 0. Their exact score-B obligations are C: `k+1 ≤ B`, D0: `k+1 ≤ B`, D2: `k+2 ≤ B` for every corresponding `HaltsAfter` time.
