# q0-149 frozen frontier index 8: exact two-block growth

Machine `1RB1LC_1RC0LC_0LA0RD_1RF1RE_0RB---_1LB1RE`; hole E1. All returns avoid the hole, so every completion is nonhalting.

Use the ordinary Z0 zipper (left includes scanned symbol; each side is nearest first). At step 34254 the blank orbit is exactly state C, left word 0, right word A M F, where
- P = 010101010100000101010
- B = 010101010 (9 bits)
- A = P without its first bit, followed by seven copies of B
- M = 1010101001000100100010100000001
- D = 0010001 (7 bits)
- F = 00100000101000001001101010001010001001010100010101010101000001010001001

Define fam(n,m) as C with left 0 and right A B^n M D^m F. The exact symbolic certificate gives a positive return of 480n+6112 steps, for every n,m >= 0. Its output right word is A X (Y X)^n Y M D D^m F, where X=01 and Y=0101010, so B=XY. By induction X(YX)^n=(XY)^n X, the target is fam(n+1,m+1). No test of either variable exponent is used. The 8 verified local sweep identities have costs 41,79 repeated four times; all remaining 6112 steps are exact symbolic steps. Consequently fam(0,0) lies in a positively returning region, and E1 is never consulted.

Reproduce: node generate-q0-149-index8.cjs (from this directory). It checks exact symbolic source/target equality and cost, plus the exact blank seed. The proof of the variable sweep identities is repeated finite substitution on untouched tails. A generated Lean formalization is in generate-q0-149-index8-lean.cjs; kernel acceptance is pending.

This is the fourth mathematical closure among the five long q0-149 holdouts (indices 11,16,17 also closed by separate return proof). Index 10 is still open. No parent Cover is yet claimed.
