# Clean proof of Sheep P-family theorem

Notation: P_b=(2^(b+1)+1)/3 for even b>=4, and f is the published Sheep one-variable map from initial 5. The complete existence table is given in TheoremA.md.

A normal-branch predecessor n=2^a*m with odd m>=5 must satisfy:

    2^(b+2) + 5 - 6*a = 3*(2^(a+1)+1)*m.    (A1)

Put D=2^(a+1)+1. Thus 2^(b+2)=6*a-5 modulo D. As 2^(a+1)=-1 modulo D, the residues of powers of 2 modulo D are exactly among 2^r or D-2^r, 0<=r<=a.

For a>=5, induction establishes 6*a<=2^a. Hence the positive odd number 6*a-5 is greater than 1 and below 2^a, so it is neither 2^r (1 or even) nor D-2^r (at least 2^a+1). For a=4, D=33 and the residue set is {1,2,4,8,16,17,25,29,31,32}; it omits 19=6*a-5. Therefore a<=3.

For a=0,1,2,3, condition A1 requires 2^(b+2)=6*a-5 modulo 3*D. The four moduli are 9,15,27,51; the multiplicative orders of 2 are 6,4,18,8. The allowed b+2 residues are respectively 2,0,16,6, yielding b=0 mod6, b=2 mod4, b=14 mod18, b=4 mod8. Conversely, each condition makes m=(2*P_b-2*a+1)/D integral and odd. For the least b values 6,6,14,12, the resulting m is at least 5; it increases with b. Thus each congruence is sufficient.

A special odd-part-3 predecessor would require 2^(b+1)=9*2^a+3*a+8. For a=0, the right side is 17. For a>=1, induction gives 3*a+8<7*2^a, so the right side is strictly between 2^(a+3) and 2^(a+4). This cannot be a power of two.

For b divisible by 8, only b=0,24,48 modulo 72 can satisfy the a=0 row; only b=32 modulo72 can satisfy a=2; rows a=1 and a=3 are impossible. Thus b=8,16,40,56,64 modulo72 are permanently source-free. Since each such P_b differs from the true initial 5, it cannot occur on any finite blank-entry orbit. QED.

Proof applies to the published map. It has not yet been kernel-verified.
