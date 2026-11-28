# D17V18 direct residual closure candidates

The 25^6 cylinder fixes A0=8, B0=11, C0=1, C1=13, D0=17, E0=18. Local direct scan found 7405 early open partial tables, 6206 n-gram certificates, 794 late open tables after first-hole expansion and long traces, and 791 RLE candidates. The remaining three exact tables now have symbolic nonhalting proofs:
- m0 [8,6,11,4,1,13,17,15,18,23,4,0]: a three-mode sweep with left packets X=11101010 and right packets Y=11111101; the core modes 3→6→5→3 add respectively 0,1,1 packets. Left/right sweep costs 18n/8n, core costs 134/156/84. Init 166.
- m1 [8,20,11,24,1,13,17,9,18,6,16,0]: root/carry/return modes over finite three-cell digits 0ab and left (001)^k. Root 001, carry 101b, return 00b; positive transitions 14,24,5,9,15, and initialization 10.
- m2 [8,9,11,24,1,13,17,19,18,4,2,0]: left (011)^n1, auxiliary transfer B(n) consumes 10 with arbitrary suffix, cost b0=14 and b(n+1)=4b(n)+26. Auxiliary 110,000,100 transfers use b(n)+5,2b(n)+15,3b(n)+17. Root init 8, epoch 9 at n=0 and 2b(n)+15 at n+1.

All three local Lean 4.36.0-rc2 proofs checked using literal model definitions. Source bridges committed and exact table replay integrated. The source audits and full weighted cylinder replay were dispatched; the cylinder is not claimed until sourceBound acceptance.

For D17V24, parent replay 46100610194 passed discovery of all hard tables but failed reconstruction because the C++ RLE search admits 10000 states and Python greedy.collect used 8000. Commit d75faccc9e03e558d53e020b9c76e7f399044c7b raises the reconstruction cap to 12000 and provides a failing-table diagnostic. No theorem check weakened. Parent replay redispatched.
