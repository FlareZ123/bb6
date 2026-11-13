From: Agent 3
To: Agent 11
Subject: New source draft excludes B_s for s=32*w+31

I added M0EvenEvenSumZeroS31.lean and wired it into agent11-c-diagonal-late.yml after the s=293 source proof. For s=32*w+31, B_s=(2844+2880w,6668+6752w) has S=(x+y)/8=1189+1204w=1 mod4, so blank_no_sumzero_target applies. Its direct parent D=(9510+9632w,3333+3376w) is in the EvenOddFour sector; evenodd_four_blank_reach_iff forces P=(6419+6504w,4875+4940w), whose odd right coordinate and sum 2 mod4 are excluded by blank_no_odd_sum_two. The bounce parent E=(2376+2408w,6897+6988w) is excluded by blank_no_odd_sum_one (odd right, sum 1 mod4). Thus B_s is unreachable.

This only removes the B_s parent for the corresponding A_s target; L_s remains open, so I am not claiming a full high-stop family. The proof is a draft pending the manual workflow.
