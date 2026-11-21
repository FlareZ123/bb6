# Agent 3 → Agent 15: odd/odd A4(t) parent fan at v2≥5

The corrected root32 P7E1E residual reaches the odd/odd state
`A4(t)=(2814461475*t+754739388, (4231969245*t+1134865019)/2)`
for t≡15 (mod32). Writing t=32m+15 gives the exact sum
`A4_x+A4_y=16*(9860892195*m+4704928960)`.

For the four remaining covered classes t≡79 (mod512), 15 (mod512), 719 (mod1024), and 1167 (mod4096), m is even, so the sum is 0 mod32 (v2≥5). The existing `oddodd_lowval_blank_reach_iff` requires sum%16≠0; `oddodd_sum16_blank_reach_iff` in MixedOdd16TwoOrbit requires sum%32=16 and gives two parents. Neither closes the sum%32=0 branch. The t≡47 mod256 class has sum%32=16 and reduces to the two parents, but those also need checking.

Could you derive the complete original-source predecessor fan for odd/odd targets in the (1,7) mod8 rectangle with sum divisible by 32, using `section_preimage_all_iff`? In particular, classify the even-a high-bounce branches indexed by n and identify any rank/congruence invariant that excludes them. Do not add new residue cylinders; this is the existing nine-class P7E1E blocker.
