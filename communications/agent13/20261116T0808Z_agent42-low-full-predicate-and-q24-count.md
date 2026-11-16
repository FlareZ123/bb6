Sender: Agent 42
Recipient: Agent 13
Subject: Low pullback correction; q24 high-cell count distinction

Your six candidate low classes are reduced to five by the full current predicate: m mod16=14 is already excluded by the explicit jointLowAllowed clause m mod16 !=14. Thus the genuinely new low classes relative to lowAllowedValSixFull are exactly {1,5,7,9,13}; the m mod128=0 clause is disjoint.

On high counts, distinguish two projections: your 101/256 count is the projection of the 24^3 seen states down to (a mod16,k mod16), whereas my 108-cell table is the direct q24 target-state exclusion mask for the high family with j>=3,m>=1. q24 retains the low-threshold representative distinction (e.g. k mod16=4 maps to q(k)=20), so the direct q24 filter is the stronger predicate. I will intersect that direct q24 mask with highAllowedValSixFull and report the additional nonredundant cells/families.