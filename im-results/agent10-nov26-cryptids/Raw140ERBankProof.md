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

## Depleted-bank exit (derived 04:25 UTC)

For n,p>=0, after the bank has been depleted, there is a second common-table
identity:
ER(1 (133)^(n+2) 3^p2,s)
 -> AR(3^(p+11)2,(115)^(n+epsilon(s)) rho(s)),
where epsilon=1 exactly for s=11511. This holds with all three
A1/F0/F1 entries undefined. Proof uses the six preparations above.
Write j=k from the preparation table, and Y its right suffix. The path
EL3^(j+1) EL1 DR1 EL7 gives
ER(333 (133)^(n+1) 3^p2,1^(j+1)Y), cost 5+3(j+1).
The path ER1 EL3^3 EL1 DR1 EL7 gives
ER(333 X,1115 Z) from ER(333133 X,1 Z), cost 21.
Iterating it n+1 times yields
ER(3^(p+3)2,1115 (115)^n 1^jY).
Finally the homogeneous path
ER1 EL3^(p+3) EL2 BL0 CR1^(p+4) CR5 BL6^(p+4) BL4 BR2^(p+5)
BR1 DL5^(p+6) DL0 AR4^(p+6) AR0 DR1 EL7 ER1 EL3^(p+7) EL2
BL0 CR1^(p+8) CR5 BL6^(p+8) BL4 BR2^(p+9) BR5 DL5^(p+10)
DL0 AR4^(p+11)
has cost 36p+298 and produces AR(3^(p+11)2,(115)^n 1^jY).
For the first five preparations 1^jY=rho(s); for the last it is
115 rho(s). The local paths were symbolically generated with an opaque
suffix, not sampled; Raw140ERExit.lean expresses the composition.

This connects to the six **accepted** affine conversion identities in
Raw140VariantLoops.lean, CI 45937613031 (commit
4d68aee93fd9d59e049cac03525bee6d8dfa5bc6):
* IDs 28,81,86: AR(3^p2,115Y) -> AR(3^(p+5)2,Y), costs 18p+83
  (28,81) or 18p+81 (86).
* IDs 39,77: AR(3^p2,(115)^2Y) -> AR(3^(p+12)2,Y), p>=1,
  costs 54p+384 (39) or 54p+382 (77).
* ID 88: AR(3^p2,(115)^2Y) -> AR(3^(p+10)2,Y), cost 36p+254.

Thus the previously expensive transition from a whole left bank to the
variant-specific A1/F0 branches is reduced to affine updates plus a
finite suffix. The two-triplet variants retain a parity bit.

## 2026-11-27 11:26 UTC: sibling 42 depleted-defect exit

The common nine-row table also admits, for p>=1 and arbitrary right suffix Y,
ER(33325 3^p 2,1115 Y) -> AR(3^(p+12) 2,115 Y), cost 54p+403.
The symbolic path is generated as finish42 with p-1 as its Lean parameter in generate_raw140_er_suffix.js. This path does not inspect Y. CI run 45989547335 compiled the generated local file and Raw140ERSuffix.bank successfully, before failure in the separate exit composition. The current exit composition is being repaired; its last successful subtheorems are not yet a new root verdict.

Combine the accepted sibling-42 conversion (AR(3^p2,(115)^n Y) -> ER(1(133)^(n-1)25 3^p2,Y), time 37+45(n-1)) with the six suffix preparations, prepareCarry, tripLoop, pump and finish42. For p>=1,n>=3, this yields the candidate exact macro return
AR(3^p2,(115)^n s) -> AR(3^(p+12)2,(115)^(n-2+epsilon(s)) rho(s)).
Correction: the emitted 115 from finish42 makes the correct exponent n-2+epsilon(s), since the pump consumes n-3 carry triplets. Cost is 37+45(n-1)+prep(s)+5+3(k(s)+1)+21(n-2)+54p+403. This is a finite phase, not a closed invariant. The case n<3 is the next substantive bottleneck. Do not infer nonhalting from this phase alone.

Separate source result: exact sibling id36 (1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---) is covered by BB6.Agent10Nov26.n12_cover from Nov26Pair2.lean. Pinned upstream source audit 45989202041 SUCCESS; n12_eq, n12_never, n12_cover all have only propext, Classical.choice, Quot.sound. This is a proved one-hole cylinder (25 completions), but the generated three-hole cut has not yet consumed it, so its checked remaining_count is still 20. The companion n8_cover also passed.
