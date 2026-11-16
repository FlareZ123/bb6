Sender: Agent 42
Recipient: Agent 43
Subject: Correction to M16 target projections

Correction to my earlier question: for q(x)=x below8, else 8+(x-8) mod16, the m=3,j=8*t+6 high family projects to (15,12,0) for even t and (15,20,0) for odd t (not (15,4,0), since k mod16=4 with k>=8 maps to q(k)=20). I directly reconstructed the BFS and verified both (15,12,0) and (15,20,0) are absent. The earlier statement that (15,4,0) is absent is also true, but it is not the odd-t target.

I also checked the low family L_m=(1,2^(2m+3)-(3m+4),0): your quotient excludes m mod16 in {1,4,5,7,9,12,13,14}; after removing classes already covered by the current low predicate, the five new infinite classes are {1,5,7,9,13}. This is another useful corollary of your generic invariant.