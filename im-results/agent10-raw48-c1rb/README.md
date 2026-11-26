# Raw48, C1 = 0RB: six-hole exact-bound candidate

Parent `1RB---_1RC---_0RD0RB_1LD1LC_------_------`, initial cut 4. This is one ordinary-action child of the seven-hole Raw48 parent (D1=1LC), whose first hole is C1 at time 6. Raw completion mass 25^6 = 244140625. Candidate weighted maximum 157; a full attaining table is `1RB0LF_1RC0RE_0RD0RB_1LD1LC_0RC1LF_1LAHHH` at n=156 and d=0.

## Evidence status (17:16 UTC)
- The new `ZipCanonicalAudit.lean` checker and composition theorem compile against the exact original Lean source bundle (revision d4f8af6c95aa037f2a1a195301471bdacb1c78c2, artifact 15082864386); standard axioms only.
- The full raw tree has 8424 splits, 163783 cycle leaves, 29088 last-hole leaves and 882 open leaves. After using original source TNFSupport/first-use symmetry, the retained tree has 4214 splits, 81922 cycles, 14544 last-hole leaves and 441 open leaves. All 441 have concrete candidate witnesses: 436 FAR and 5 symbolic sweeps. The ten sweep proofs (including swapped E/F duplicates) were locally kernel-accepted; the full weighted proof is compiling, not yet claimed.
- `spec.json` pins the ordered canonical open list, witness index and all ten sweep tables. The original enum cap is merely a search parameter, not a claim of bounded nonhalting.
- Independent direct enumeration of the six-hole parent reproduces the pinned raw open-list SHA256, counts, and maximum.

The source-certified cover, if accepted, will apply to this exact six-hole cylinder only. It does not close all Raw48 or reduce the count of whole-parent residuals.
