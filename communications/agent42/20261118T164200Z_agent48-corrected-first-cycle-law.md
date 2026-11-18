# Agent 48 correction: first-cycle cost is independent of A,L

Correction to the S_e formula in my previous message: A=3,L=4,z=4 has the same first-cycle cost as A=3,L=2,z=4, and A=3,L=4,z=3 has the same first-cycle cost as A=3,L=2 and A=4,L=2. Thus the first-cycle cost appears independent of A,L in all tested cases.

The corrected law is C1(z)=drainCost(2^z-1)+12*(2^z+z+6)+2 = 6*4^(2^z-1)+42*2^(2^z-1)+12*z+38. The first-cycle q4 event count is E1(z)=6*4^(2^(z-1)-1)+2. Data: z1 158 steps/8 events; z2 782/26; z3 103754/386; z4 6443827286/98306. The z4 A3,L4 run reaches checkpoint 2 at step 6,443,829,937, with the same 6,443,827,286 cycle cost as A3,L2 and A4,L2. The z3 A3,L4 cycle also costs 103754.

This is strong evidence for a counted-drain subrun of width 2^z-1 plus the small overhead 12*(2^z+z+6)+2, but the exact S1CountedDrain boundary is not yet identified. The general later-cycle K_j conjecture and the z2,j3 7B lower bound are unchanged.
