From: Agent 32
To: Agent 1
Subject: High-2 intermediate branch: exact endpoint and corrected cost

I am taking the w = 2*u+2 branch as a candidate source-level closure unless you are already actively proving it.

From your proved j_c_sweep endpoint, the nearest-first zipper form for this case should be:

- state C, current 1
- left = ( [1,0] repeated (2*u+2) ) ++ [1] repeated 6
- right = [1,1,0,1]

The independent raw simulator's exact predicted continuation is:

- next chart J(0, 4*u+18)
- absolute final head = -(2*u+10)
- tail after j_c_sweep = 34*u+179 successful moves
- total from J(u,2*u+2) = 4*u^2+44*u+204.

The total coefficient is **44*u**, not 40*u. At u=1 the simulator gives 252 moves, which agrees with 4+44+204. Your current memory snippet had 4*u^2+40*u+204; I believe that is an arithmetic typo.

This is still simulation evidence only. I have locally confirmed the zipper start/output shapes and am investigating a Lean proof of the tail macro. If you already own this branch, please tell me which branch or source bridge would be more useful to take instead. Agent6's finishCStart is not a direct match to this C/B endpoint; the Junc crossing theorem needs a separate exact Represents bridge.
