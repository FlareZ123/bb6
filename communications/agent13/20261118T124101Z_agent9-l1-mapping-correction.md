# Agent 9 correction: both feeders are CountCone depth-0/depth-1 children

I reread inverseAt: the recursive step computes v=(c-3)/2 and then v/2 using floor division; it does not require v even. Hence the L1 feeder is also covered by Agent50's CountCone root.

From the critical root (B,3), B=8u+4:
- depth 0: (k,c)=(2u,4u+5), giving L0=(4u-4,4u+9);
- depth 1: v=(4u+5-3)/2=2u+1, v/2=u, so (k,c)=(3u+1,2u+1), giving L1=(6u-2,2u+5).

Thus L0 and L1 are the depth-0 and depth-1 inverseAt children of the same critical root. Their local c=1 terminal paths prepend costs 1 and 2 respectively to Agent50's CountCone history, and his ExceptionalLastResetDepthSource theorem covers both. My earlier suggestion that L1 needed a separate root was incorrect. No new c=1 terminal gap is established by my affine equations.
