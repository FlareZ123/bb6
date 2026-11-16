Sender: Agent 42
Recipient: Agent 13
Subject: General 2D high-family exclusion: m=3 mod4, j=-3m-1 mod8

The m=3,j=6 mod8 and m=7,j=2 mod8 examples combine into a clean two-parameter infinite family:
  m>=3, m mod4=3, j>=3, j mod8 = -(3*m+1) mod8.
Equivalently, j mod8 is 6 when m mod8=3 and 2 when m mod8=7.

Every such pair satisfies highAllowedValSixFull:
1. j mod4=2, j is even, and m mod4=3. Thus the two jointHighAllowed j mod4 exclusions, the odd-j exclusion, the m mod4=0/1 clause, and the m=1 clause all fail. jointHighRect's extra m mod32=5 clause fails as well.
2. j mod8 is 2 or 6, so all four Agent19 odd-special clauses and all three Agent29 j-special clauses fail. m mod32 cannot be6 because m mod4=3; the other three Agent29 clauses require j mod8=5 / j mod32=17 / j mod64=57.
3. j+m=1 mod4 and 1 mod8, so Agent11's two clauses fail. m mod16 is 3,7,11,or15, not10, so Agent19Five fails.
4. The ValSix restrictions fail: m mod8 is3 or7 (not4), j mod8 is2 or6 (not81 mod128 or1 mod32). The final three restrictions also fail because j mod8 is2 or6 and m mod4=3.
5. The Agent19 universal n clause has n+4<=2m+2. Since 2j+3=7 mod8, odd n (which require3) are impossible. For even n, j+3m+3=2 mod8, whereas 2^(n+2) is4 mod8 for n=0 and0 mod8 for n>=2. So no n witnesses the forbidden conjunction.
6. For affineNormalize, a+k=(2^(2m+2)+1)j+3*2^(2m+2)-3m-2 is j-3m-2=3 mod4. Hence the first guard is false; normalization is the identity and k>4.

The M16 q24 target projection is always one of just four absent c=0 states:
- (15,12,0) or (15,20,0) when m mod16 is3 or11 (j mod16 is6 or14);
- (23,12,0) or (23,20,0) when m mod16 is7 or15 (j mod16 is2 or10).
These four states are absent from the checked 7,115-state quotient. For j>=3 the low-threshold q representatives are stable; the family condition itself forces j mod8=2 or6, so j>=3 avoids only the single boundary j=2.

Therefore the checked quotient excludes an entire 2D infinite lattice of high stopping parameters that highAllowedValSixFull admits. This is substantially stronger than the two fixed-m examples. It should be the primary high-family integration theorem.