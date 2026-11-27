# Arbitrary-word left-bank transduction for the Raw140 common table

This is a mathematical derivation, with Lean formalization in Raw140ERSweep.lean,
Raw140ERSuffixLocal.lean and Raw140ERSuffix.lean. It does not itself prove
nonhalting of any of the remaining 19 siblings. Kernel status must be read
from the erSuffix CI job rather than inferred from this note.

Use the common nine-row partial table of Raw140Orbit.base and three-bit
blocks in nearest-first order. E_R/E_L mean the head is at the corresponding
block boundary. X,Y are arbitrary tapes represented by block lists.
W is any finite word on {1,3}. No transition A1, F0 or F1 is used.

## Local rotation

The five exits ER1 EL1 DR5 EL7 ER5 give
ER(1X,1Y) -> ER(13X,Y), cost 19, and iteration gives
ER(1X,1^pY) -> ER(1 3^p X,Y), cost 19p.

The exits ER1 followed by EL3 repeated p times give
ER(3^p X,1Y) -> EL(X,1^p5Y), cost 7+3p.
Taking X=5X', followed by EL5, the 19p iteration, and ER5, gives
ER(3^p5X',1Y) -> ER(11 3^p X',Y), cost 22p+15.

For every W and p>=0,
ER(3^(p+1) W5X,1Y) -> ER(11 3^p W3X,Y),
cost 22(p+1+|W|)+15.
Proof: induct on W with p and Y arbitrary. Empty W is the previous
identity. Initial 3 is absorbed into p. Initial 1 permits the carry
ER1 EL3^(p+1) EL1 DR1 EL7, cost 12+3(p+1), leaving
ER(3 W'5X,1^(p+1)5Y). Apply IH with p=0 and right suffix 1^p5Y,
then the 19p iteration and ER5. The final left stack is 11 3^p1 W'3X,
and total cost is the stated formula.

A second induction, using the same carry without initial ER1, gives
EL(3^(k+1) W5X,Y) -> ER(1 W3X,1^kY),
cost 22|W|+3k+23. For empty W, sweep EL3^(k+1), exit EL5,
then apply the 19-step local rule. For initial 1, use
EL3^(k+1) EL1 DR1 EL7, then the p=0 rotation above. For initial 3,
use IH at k+1 and apply the 19-step rule once.

## Six suffixes

The finite preparatory paths are generated in Raw140ERSuffixLocal.lean.
For ER(1Z,s), with arbitrary Z, the preparations produce EL(3^(k+1) Z,Y):

| s | k | Y | cost |
|---|---:|---|---:|
| 542 | 1 | 52 | 24 |
| 152 | 1 | 121 | 48 |
| 1121 | 0 | 5215 | 65 |
| 5215 | 0 | 1155 | 37 |
| 1155 | 2 | 511 | 87 |
| 11511 | 2 | 5542 | 109 |

Take Z=W5X and apply partial rotation. For the last row only, apply
the 19-step rule twice and ER5, adding 45 steps. Consequently,
ER(1 W5X,s) -> ER(1 carry(s) W3X,rho(s)),
where rho rotates the listed six suffixes, carry is empty except on
11511->542 (then carry=133), and costs are 22|W|+c_s with
c_s=50,74,88,60,116,183 respectively.

## Bank theorem

Let rank(s) be zero through five in the listed order and
C_n(s)=floor((n+rank(s))/6). Iterating the last identity proves

ER(1 W5^n X,s) -> ER(1 (133)^C_n(s) W3^n X,rho^n(s)).

The tape outside this bank is completely arbitrary. Each iteration
increases the intervening odd-word length by one, with three extra
blocks on the wrap. Exact primitive cost, if needed, is
sum over i=0..n-1 of 22(|W|+i+3 C_i(s))+c_{rho^i(s)}.
The proof is an induction, not a fit to finite simulation data.
For n>0 the time is strictly positive. Since the common table is
partial, all these identities lift to every completion.

This complements the right-bank arbitrary-word bounce for alphabet
{4,6} in Raw140DoubleGrowthProof.md. Remaining task: identify a closed
global orbit using these two bank transductions and the variant-specific
A1/F0 conversions; neither bank alone is an infinite recurrence.
