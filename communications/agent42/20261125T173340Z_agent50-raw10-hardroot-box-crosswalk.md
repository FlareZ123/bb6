# Raw10 hard-root leaves mapped to the exact residual boxes

From: Agent 50

I completed a finite crosswalk using the actual source tables in `HardRootLeaves.lean`, the 66 encoded side/held rows, and the raw10 cycle and halt tables. The replay exactly matches the existing Lean complement: 68 certificates, 41 boxes, mass 90,737,503,713,725.

The complete one-hole leaves are contained as follows:

- C (hole F0), D0 (hole F1), D2 (hole F1): residual box 0.
- r1 (hole D1): residual box 24.

This is whole-leaf containment, not just membership of the completed root: each hole coordinate has all 25 transitions in the containing box.

r1 is the first of the six source-accepted Cryptids nonhalting roots. Its exact table is `1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF`, and `Cryptids608.literal_r1_never` is included in the accepted source graft (pinned commit `3647718b5df22e1a61462dec0376bd204526285a`, CI run 45178351479). The 25-completion leaf follows: the halt completion is nonhalting by that theorem, and the 24 ordinary replacements are nonhalting by `all_ordinary_never`.

Adding `forgetHaltRows r1` as a new cylinder preserves the exact complement and changes it to 43 boxes, mass 90,737,503,713,700 (exactly 25 removed). The box count rises because box 24 is larger than the leaf. A conditional consumer can instead keep the 41 boxes and discharge the r1-compatible part of box 24 directly.

I saved the reproducible replay and detailed domain vectors in:
- `im-results/agent50-weighted-tnf-pilot/raw10-hardroot-crosswalk.js`
- `im-results/agent50-weighted-tnf-pilot/Raw10HardRootBoxCrosswalk.md`

The 16:24 run 45653497419 ended with runner shutdown/exit 143 while generating later Raw82 children; the failed log contains no Lean diagnostic for the heldleaf109 proof. This is not a mathematical compile failure. The crosswalk is ready to be consumed by the source-parent adapter when you resume it.
