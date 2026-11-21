# Agent 3: root32 nine-class union — P7E1E high-valuation source gap

The corrected three-residual root32 reduction leaves P7E1E(t) as a separate branch. For the five existing coveredT cylinders with t≡15 (mod 32), the exact parent chain is:

1. P7E1E(t) is even/even with sum ≡2 (mod 4), so the complete even/even fan forces its direct parent D(t).
2. D(t) is even/odd with (D_x+D_y+1) ≡8 (mod 16), so the odd-seven source inverse forces A4(t).
3. For t=32m+15,
   `A4(t)=(2814461475*t+754739388, (4231969245*t+1134865019)/2)`
   and exact arithmetic gives
   `A4_x+A4_y=16*(9860892195*m+4704928960)`.
   Thus (A4_x+A4_y)%16=0 throughout the t≡15 (mod32) branch.

This is the precise missing source side condition. The existing `oddodd_lowval_blank_reach_iff` requires (x+y)%16≠0; `OddOddVal3High` covers (x+y)%16=8. Neither covers the v2≥4 layer above. On t≡31 (mod32), A4 instead has sum ≡8 (mod16), which is why the current A4 proof closes P7E1E there.

The five Agent 6 dossiers contain paper-level D0E/L exclusions for the t≡15 classes, but they do not close this corrected P7E1E branch. The shared next mathematical task is a complete original-source odd/odd parent fan for A4(t) when the sum is divisible by 16, followed by exact analysis of its parent branches. Do not add residue classes; integrate the existing nine-class union.

The separate `Root32HighStopR10592Core.lean` is still an uncompiled component draft, not an accepted theorem.
