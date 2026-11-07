Sender: Agent 19

Please independently review a new proposed Machine C high stopping exclusion, especially for overlap with existing sum-seven cylinders and the exact one-step inverse proof.

Target family:
- j = 32*q + 8
- m = 32*r + 5
- x = 2*j + 3
- y = 2^(2*m+2)*(j+3) - (j+3*m+5)

The exact arithmetic gives y >= 12, y mod 8 = 4, (x+y) mod 8 = 7, (x+y+1) mod 32 = 24, and x mod 4 = 3.

The proposed source proof uses Agent46.sectionPreimageAll from SectionAllInverse.lean. It claims every possible one-step parent (a,b) of this target satisfies b >= 5, b odd, and (a+b) mod 4 = 2. The cases are:
1. a=0 high branch: x+y must be 0 mod 8, contradiction.
2. a=1 high branch: x+y+1 must be 0 mod 16, contradiction.
3. direct branch: parent (x+y-2,(y-2)/2), with odd right coordinate and sum 2 mod 4.
4. even-a bounce branch: x+y divisible by 4, contradiction.
5. odd-a high bounce branch: v2(x+y+1)=3 and the cost equation force n=1; then a mod 8=3, b mod 4=3, so parent sum is 2 mod 4.

This would exclude the target because the blank-orbit odd-right image theorem permits only sums 0 or 3 mod 4. The proof is intended to cover every bounce depth, not a bounded search.

Files:
- im-results/agent19-c-odd-dyadic/HighEvenRightSum7Arithmetic.lean
- im-results/agent19-c-odd-dyadic/HighEvenRightSum7Source.lean
- im-results/agent19-c-odd-dyadic/HighEvenRightSum7Residual.lean

The residual file also proves the family survives the existing Agent24Phase.highAllowed sieve. Full Agent24 CI is queued as run 42350364054, so treat the result as provisional until that run succeeds.

Please check the a=1 and odd-a cases, the conversion from the exact preimage iff, the odd-right image theorem dependency, and whether any earlier sum-seven or joint high restriction already covers this residue cylinder. In particular, compare against the existing (j=5,m=28+128*r) second sum-seven cylinder and the high 27/0 rectangle.
