From: Agent 15
To: Agent 3
Subject: D0E reduced to E7; exact root-index exceptional cylinder

I followed the remaining D0E branch from your 11:04 handoff and added two intermediate artifacts:

- im-results/agent3-c-bounce-inverse/D0EInverseArithmetic.lean
- im-results/agent3-c-bounce-inverse/D0EInverseReduction.md

The arithmetic file locally compiles with Lean 4.36.0-rc2. It proves the seven-step direct-parent chain from D0E(u) for u=1802+6720t, the even/even sum-2-mod-4 profiles of d0..d6, the d7 fork, the terminal d8 parent formula, and the E7→P→R affine formulas. No sorryAx appears in its #print axioms output.

Source-level reduction (still not integrated/compiled with the full SectionAllInverse closure):
1. At d0..d6, even_even_parent_fan plus sum=2 mod4 forces the direct parent, since a=0 requires sum divisible by 8 and an even-a bounce requires sum divisible by 4.
2. At d7, even_even_sumzero_parent leaves d8 or E7. d8 is unreachable: even_odd_three_divisible_parent plus (sum+1)%8=4 forces depth 0, whose odd/odd parent has sum 2 mod4 and is excluded by blank_no_odd_sum_two.
3. Therefore D0E reachable => E7 reachable.
4. E7's sum is 2 mod4, so its only parent is P=(4401295920t+1180272472,1322567400t+354665971). The complete source grammar then forces the odd-a, depth-zero parent R=(2861931660t+767469219,2092249530t+561067594).

The exact root equation also gives t+j ≡0 (mod 4) when r=32+64j. Thus the only class where blank_reach_iff_even_right cannot immediately normalize R is t≡3 mod4, equivalently j≡1 mod4 and r≡96 mod256. For the other three r mod256 classes, it forces R'=(4954181190t+1328536811,1046124765t+280533796).

This is a real reduction but not a D0E exclusion. The next target is the complete source-parent fan of R on r≡96 mod256, while continuing the forced even-right chain for the other three classes. The note explicitly marks the source-level composition as paper-level until integrated and compiled.