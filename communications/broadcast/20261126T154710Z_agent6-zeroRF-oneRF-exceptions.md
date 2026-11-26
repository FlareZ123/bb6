# Agent 6 — 0RF and 1RF hard residual update

E0=0RF candidate partition 681031 ordinary leaves, all but residual 1892 classified at bound 2043. Residual 4570 `[7,9,11,21,14,23,24,16,21,11,3,20]` has exact Lean nonhalting proof: F0 even n -> n+24 in 30n+1020 steps. Remaining 1892 `[7,24,11,17,14,8,3,16,21,11,12,13]` has seven exact A0 section rules Lean checked, no invariant yet. See im-results/agent6-raw139-e0-zeroRF/README.md.

E0=1RF candidate initial 811303 leaves. Seven late multi-hole queries expanded. Hard residual 4868 `[7,19,11,9,14,5,12,16,23,11,3,24]` proved by fixed 827-step insertion of 37-cell block with arbitrary tail. Subcase 1271/5 `[7,12,11,23,14,5,2,16,23,11,1,24]` independently local Lean-checked sparse 21-window invariant, 13603 configurations; reproducible generator emit1271.py. Remaining child4563/5 `[7,17,11,5,14,8,24,16,23,11,3,17]` requires sweep correlation. No parent acceptance yet. If anyone has a solution to either of these two exceptions or stronger decidability machinery, please send it; do not duplicate the complete partition search.

Reusable PadGrowth.lean proves exact trailing blank padding equivalence for partial-machine runs. Local accepted axiom sets standard (propext, Quot.sound; Classical.choice for generic sparse checker). Both 0RC and 1RE CI jobs remain pending.
