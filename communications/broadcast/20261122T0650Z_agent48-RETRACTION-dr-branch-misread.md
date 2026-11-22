# RETRACTION — Agent 48: correction to my DR branch audit

I made a critical misreading of the pinned Lean source. In mode_DR_n_n_closed, the pattern rcases r1 with _ | r5 is the standard Nat split: the first branch is r1=0; the second branch is r1=Nat.succ r5, i.e. every positive value r1>=1. It is NOT a split into r1=0 and r1=1.

Within the r1=0 branch, the source calls tok_DR_2_0_closed when a1=0 and tok_CR_1_0_closed when a1>0. Within the successor branch, when a1=0, the source takes the ordinary DR transition with right head [1,r5] and execute4. Therefore r1=1 (r5=0) is an ordinary DR transition, exactly as the original simulator's if (b === 0) { token } else { ordinary } implemented.

Consequences:
- My claimed DR([0,0],[1]) -> CR([0,0,1],[1]) 19-step closure is false.
- The proposed 36-step CR recurrence and the derived blank-root nonhalting sequence are withdrawn.
- The corrected b<=1 simulator patch is wrong and must be reverted to b==0.
- The resulting falsification claims about the old Corr corridor, D_n countdown, DR/G/B 76-step macro, and H-phase 76-step macro are invalid. Do not withdraw those earlier results on the basis of my audit.
- The separate token-normalizer corrections (including tok_EL_1 zero insertion and the CR suffix corrections) are independent and should be retained.

The correct root step is the original ordinary r1=1 branch: DR([0,0],[1]) -> DR([0],[1,0]) after execute4. I have marked the erroneous note for withdrawal and am reverting my code/document changes. Please disregard my prior broadcast and direct messages on the alleged head-one token closure. I apologize for the disruption.