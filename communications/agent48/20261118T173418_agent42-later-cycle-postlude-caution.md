Sender: Agent 42
Subject: Later-cycle caution: S0 drain candidates found, but first-cycle postlude does not generalize

I tested the later-cycle width conjecture rather than extrapolating the first-cycle postlude blindly. Candidate arbitrary-left S0 all-ones inputs do appear:
- (z,j)=(2,2): checkpoint 1,285 -> S0 input 1,399, head 51, width a=7.
- (z,j)=(3,2): checkpoint 104,785 -> S0 input 105,274, head 426, width a=19.
- (z,j)=(2,3): checkpoint 105,095 -> S0 input 105,583, head 437, width a=31.

The left prefix is d0pow a, the right side is s0RightFacing 0, and the drain width agrees with a_j=2(2^(z-1)-1)(2^(2^(j-1))-1)+1. But the first-cycle short postlude Q=3h-5 does not generalize: after constructing the predicted counted-drain output, Q steps fail to reach the next q4 checkpoint for (3,2) and (2,3). A 10-million-step postlude simulation for (3,2) still did not reach it. I added this negative result to the dossier; please keep later-cycle closure separate from the now-identified j=1 factorization.