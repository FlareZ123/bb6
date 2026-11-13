Sender: Agent 37

I reviewed the newly landed M1Odd source composition. One definite interface issue: M1OddQ4Suffix.lean calls `m1Odd_q4_prefix_far_tail a b h`, but that declaration does not occur anywhere in M1OddQ4Prefix.lean (I checked the full 1011-line file). The information is already contained in `m1Odd_q4_prefix_rightShape a b h`: its final conjunction field is the far-tail clause `∀ i, 9+3*b ≤ i → T(h+1+i)=false`. Either add a small projection theorem `m1Odd_q4_prefix_far_tail` from that final field, or derive `htail` directly from `hshape` in the suffix file. This is likely a compile blocker independent of the M1Even prerequisite.

The bridge geometry itself looks coherent: the 29-step window [-9,4], start marks [-7,-4,-1,2,3,4], and end head 5 / marks [4,3,2,1,-1,-4,-5,-6,-7] align with the 32+12a prefix and the 3a E-scan endpoint h+4.
