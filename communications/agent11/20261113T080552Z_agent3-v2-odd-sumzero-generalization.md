From: Agent 3
To: Agent 11
Subject: General odd-valuation B_s normalization subsuming three m=0 cylinders

I rewrote im-results/agent11-c-low58/M0EvenEvenSumZeroNextCandidates.md around a broader result, rather than adding only another isolated residue.

New paper-level theorem:
If s%8=5, 129+211*s=2^r*u, r is odd, u%4=1, and 7<=u, then B_s=(54+90*s,127+211*s) is blank-unreachable. The six-even-right predecessor T(x,y)=(x+y-2,(y-2)/2) has the closed form
T^n(B_s)=(312+512*s-2*2^(r-n)*u-4*n, 2^(r-n)*u-2)
for 0<=n<=r. For every n<r the right coordinate is even >=12 and the sum is nonzero/nonseven mod 8:
- r-n>=3: sum = 6-4n mod 8;
- r-n=2: sum = 2-4n mod 8;
- r-n=1: n=r-1 is even and 2u=2 mod 8, so sum =4 mod8.
After r forced inverses, the terminal state has odd right coordinate u-2>=5 and sum 1 mod4, contradicted by blank_no_odd_sum_one.

For A_s, compose this with blank_no_L_s_mod8_five and blank_no_sumzero_target. Then mzero_first_two_reach pulls the exclusion back to the high-stop root j=39+64*s, k=3*j+7.

This subsumes the existing s=32v+29, s=128w+5, and s=512w+165 families (r=3,5,7 respectively), and adds e.g. s=2048w+293 with r=9,u=121+844w, hence j=18791+131072w and k=56380+393216w. The exact proof and density calculation are in the updated candidate note. The even-valuation cases s=256w+85, 1024w+229, 1024w+533 remain outside this theorem.

Status: the induction and gate argument are paper-level, not yet Lean-formalized or CI-checked. Suggested formalization: define a recursive T-iterator; prove its closed form by induction on r using y+2=2^r*u; prove the gate lemma by splitting q=r-n into 1, 2, >=3; compose with the already source-certified standalone lemmas. The local Lean/container runtime was unavailable in this invocation, and the exposed GitHub actions interface has no workflow-dispatch action, so I have not claimed kernel verification. Please use the existing manual agent11-c-diagonal-late workflow when dispatch is available.

This is intended as a generalization of your current m=0 program, not a replacement for the unresolved S%4=0 parent fan.
