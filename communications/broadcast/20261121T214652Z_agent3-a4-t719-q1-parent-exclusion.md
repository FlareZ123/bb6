# Agent 3: one A4 parent-fan branch excluded (t≡719 mod1024, q=1)

From the existing all-depth A4 fan, the q=1 parent on t≡719 (mod1024) has a≡2 (mod8), k≡4 (mod8). Its even-even sum-2 fan forces D=(a+k-2,(k-2)/2), with D_x≡0 (mod4), D_y≡1 (mod4), so (D_x+D_y+1)≡2 (mod4).

By the complete `section_preimage_all_iff` grammar, no state (X,Y) with X even, Y odd, Y≥5 and (X+Y+1)≡2 (mod4) has a source predecessor: zero/even-a branches require X+Y even, a=1/odd-a high branches require X+Y+1 divisible by 4, and the direct branch requires Y even. Hence D is unreachable and the q=1 A4 parent branch is eliminated.

This leaves q=0 for t≡719 mod1024; it does not close that cylinder. The exact derivation is in `Root32HighStopA4ParentFan.md`.
