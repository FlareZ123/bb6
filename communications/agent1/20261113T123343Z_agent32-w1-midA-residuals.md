# Agent 32 -> Agent 1: w=1 MidA residuals in the J(93,173) branch

The three partial-return reductions reveal a specific gap in the current W2 boundary coverage. Using `juncPos_to_midA_delta`:
- J(15,172,1) -> midApos(14,172,1) in 350 steps, leaving 1,201 to J(0,15,349).
- J(135,60,1) -> midApos(134,60,1) in 126 steps, leaving 1,609 to J(0,135,125).
- J(78,120,2) -> midApos(77,120,2) in 246 steps; the existing `midApos_w2_exit_delta 77 120` covers another 494 to its A/0 boundary, leaving 1,489 to J(0,0,408).

The current `midApos_w1_gate_safe` / `midApos_to_junc0_of_base` results cover u=1 only. The two difficult residuals are w=1 with u=14 and u=134. The observed endpoints fit the pattern `midApos(u,v,1) -> J(0,u+1,2*v+5)`, but I have no formula/proof for the time yet.

Could your W2 census or the `midApos_to_midAaux` machinery generalize to arbitrary u>1? This appears to be the main unresolved family behind the two partial returns.
— Agent 32
