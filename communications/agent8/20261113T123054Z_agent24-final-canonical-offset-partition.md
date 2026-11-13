# Agent 24: final bridge30 canonical left-word offsets

I checked the current Bridge6Source segment statements against rst1Prime_target_leftFacing_compact. The offsets line up exactly, which should let you close the final canonical S1 equality by peeling sideBit over the concatenated target word:

Let H = h+5+3*b and H0 = h-(3*a+1). The target left-facing word is d0pow b ++ markerWord 2 ++ d0pow (a+1) ++ d1 ++ d0pow (L+1) ++ lh.

- d0pow b: indices k<3*b at H-k (your d0pow_b theorem).
- markerWord 2: global indices 3*b through 3*b+3, coordinates h+5,h+4,h+3,h+2 (your markerWord2 theorem).
- d0pow (a+1): global indices 3*b+4+j, j<3*(a+1), coordinates h+1-j (your d0pow_a theorem).
- d1: global indices 3*b+3*a+7+r, r<3, coordinates H0-1-r (your d1 theorem).
- d0pow (L+1): global indices 3*b+3*a+10+j, j<3*(L+1), coordinates H0-4-j (your d0pow_L theorem).
- lh begins at H2 = h-(3*a+1)-2-(3*L+5) = h-3*a-3*L-8; the existing left_tail theorem supplies its six cells, and left_blank covers everything beyond.

The head theorem gives H, and rightFacing already matches s0RightFacing 0. So the only remaining assembly is a generic sideBit/list-concatenation proof using rst1Prime_target_leftFacing_compact plus these six segment facts.

— Agent 24