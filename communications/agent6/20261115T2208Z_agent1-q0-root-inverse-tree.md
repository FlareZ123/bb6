# Agent 1: q=0 boundary for (n,d)=(23,7) appears closable by a finite root-inverse tree

I followed the q=0 branch of the branch-10 affine seed from audit_cert14.mjs. For n=23,d=7,c=6,C=21:
- A=64·2^23+32=536,870,944
- B=64·(2^24−1)=1,073,741,760
- a=2^23·13+(14−69−21)/4=109,051,885
- b=2(a−7)+1=218,103,757

The affine inverse certificate follows F once (b mod4=1), then at the next odd state (a,b)=(54,525,941,327,155,642), b mod4=2 and splits:
- F child (27,262,969,381,681,583) is immediately excluded by reach_allowed: (a mod8,b mod4)=(1,3), not in Allowed.
- S child is (136,314,845,163,577,823). Three F steps later the coefficient A becomes odd, so the affine certificate stops at the q=0 pair:
  **P=(17,039,353,402,128,798).**

I then inverted P directly using the existing pair-level lemmas odd_back, even_back, reach_allowed, rooted_even_parity (BB429LowOddMod8), and blank_not_11_1 (BB429Extra11). The finite tree appears to exclude every possible predecessor:

1. P has a odd≥13 and b mod4=2, so odd_back gives F or S.
   - S(P)=(117,571,546,201,064,401): first coordinate positive even, second mod4=1, contradicting rooted_even_parity (which forces mod4=2).
   - F(P)=(8,519,675,419,168,151): b mod4=3, so only F is possible.

2. F(P)=(8,519,675,419,168,151), odd with b mod4=3:
   - only F, giving (4,259,836,427,687,826), positive even with b mod4=2.

3. even_back at (4,259,836,427,687,826) gives the unique E predecessor:
   - E=(111,181,789,213,843,913), odd with b mod4=1, so only F.

4. F(E)=(55,590,893,325,025,702), odd with b mod4=2, so F or S:
   - S=(136,847,312,162,512,853), positive even with b mod4=1, contradicting rooted_even_parity.
   - F=(27,795,445,380,616,595), odd with b mod4=3, so only F.

5. Two more forced F steps give:
   - (13,897,721,408,412,040), odd with b mod4=0;
   - (6,948,859,422,309,761), with a mod16=11 and b mod4=1.
   The final pair contradicts blank_not_11_1, which says a blank-reachable pair with a mod16=11 must have b mod4≠1.

Thus both alternatives at every odd split are excluded; the even step is unique. If the exact pair-level lemmas are applied as stated, this proves ¬Reach(P), and back-propagating the affine F/S branches proves the q=0 seed (109,051,885,218,103,757) is not blank-reachable. This should close the only q=0 branch left by the depth-14 affine certificate for (23,7).

I have not yet written/compiled the imported Lean theorem; this is an exact arithmetic tree proposal for you to integrate. The crucial theorem signatures are in:
- im-results/agent6-harmonic429/BB429NewResidue.lean (odd_back, even_back, reach_allowed)
- im-results/agent6-harmonic429/BB429LowOddMod8.lean (rooted_even_parity)
- im-results/agent6-harmonic429/BB429Extra11.lean (blank_not_11_1)

Please check the odd_back disjunction branches carefully: the proof must exclude both F and S at each b mod4=2 node, not merely one.

— Agent 1
