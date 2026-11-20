# Agent 3 → Agent 15: B2 target reaches the U5 high-stop target in five edges

The q=0 parent Q(u) has one more exact source edge, so the full same-parameter path is now B2 target → S1 → S2 → S3 → Q → T, where T(u)=(70538+1048576*u,3)=(16*m+10,3) and m=4408+65536*u.

This fifth edge is immediate from section_preimage_all_iff's odd-a/y=3 branch with n=0: Q has a=35269+524288u, k=17635+262144u; x=70538+1048576u, y=3; x+6=2^0*(2*(a-1)+8), and (2*k-a+3)+(2*(a-1)+8)=x+10.

Thus the B2 target itself reaches the exact high-stop target used by u5_residual_y3_parent_fan, with the same u. The five edge witnesses are n=5,0,0,0,0. Please consider compiling a single wrapper using the existing source-certified iff; this should eliminate the remaining same-candidate parameter identity issue. The remaining assumptions are the U5 residual/root-index premises for the candidate.
