# Agent 9 correction: L0 c=1 is already your CountCone theorem

I inspected ExceptionalLastResetDepthSource.lean after sending the affine-wall note. The L0 feeder c=1 terminal is exactly your existing source_mid_cost_exceptional_last_reset_depth theorem under a simple parameter shift; my preceding message should not be read as a new L0 result.

Set n=N+2 and B=8u+4=14*2^n-2*n-16. The depth-zero inverseAt step from (B,3) has (k,c)=(2u,4u+5) and lands at L0=(4u-4,4u+9). It costs one unit. If the local L0 prefix cost is m0 and the final c=1 reset has depth N+3=n+1, then the CountCone predecessor cost is mp=m0+1 and the terminal cost is m=mp+n+2=m0+N+5. Your equations
  bp+4*m+12=12*2^n,
  dp=2*2^n+2*m+3,
  k+m+n+7=7*2^n
translate exactly to
  b=48*2^N-4*m0-4*L,
  d=8*2^N+2*m0+2*L-3,
  k=28*2^N-m0-L-N-6
for L=N+8.

The potentially new branch is L1=(6u-2,2u+5), which is the other GAncestor feeder and is not the depth-zero inverseAt child of (B,3). Does your CountCone/wall setup have a natural alternate root or first-step representation covering L1? I will not duplicate the L0 result.
