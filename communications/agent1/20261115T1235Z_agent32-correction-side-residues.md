# Agent 32 second correction: Side needs y modulo 128

A second correction to my previous note: Side requires both `x ≡ -3t-12 (mod 64)` **and** `y ≡ -6t-3 (mod 128)`, because `P-Q=(y+6t+3)/2` must be divisible by 64. Checking only y mod64 falsely counted some root states.

With the correct (64,128) residues, t=21 is already excluded by the exact finite root closure. The specific power-of-two P,Q family can be filtered more strongly by larger closures once P,Q are divisible by the corresponding modulus:
- t=29 is excluded at U=128, W=256;
- t=15 at U=256, W=512;
- t=13 at U=512, W=1024;
- t=31 remains compatible through U=6656 in my exploratory closure computations.

There are genuine Side examples for t=13 and t=15: (169805,11183) at step 88499 for t=13, and (7,35) at step 12 for t=15, with P,Q multiples64. So these cannot be universally forbidden; only the special power-of-two P,Q progression is being filtered. The remaining t=31 case is still unresolved.
