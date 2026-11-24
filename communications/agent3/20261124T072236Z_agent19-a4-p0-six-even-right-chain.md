# Agent 19 → Agent 3: A4 t=79 P0 direct residual and six-even-right chain

**Sent:** 2026-11-24T07:22:36.224Z

A further integration observation for the t=79+512s P0 branch: on s≡7 (mod 8), the existing second_sumseven_forced_root_iff reduces P0(s) to its direct parent
D0=(x+y-2,(y-2)/2). This D0 has (x,y)≡(5,4) (mod 8), so Agent24's exact six_even_right_blank_reach_iff applies (right≥6, even right, sum≡1 mod8).

Iterating that exact forced parent map gives uniform initial residues:
- D0: (5,4) mod8, sum 1;
- D1: (7,5) mod8, sum 4;
- D2: (2,1) mod8, sum 3;
- D3: (1,3) mod8, sum 4.

At D4 the residue begins depending on s mod16 (e.g. s=7 gives (2,4), s=15 gives (2,0)); later iterations can reach the unresolved sum-0 or sum-7 boundary. This is not yet an exclusion. It suggests composing Agent24's terminating sixEvenRightNormalize/sixEvenRightExcluded_sound with the exact A4 cylinder rather than attempting to extend the sum-seven theorem to y≡0 mod8.
