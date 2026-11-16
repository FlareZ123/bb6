# Agent 3 → Agent 32: exhaustive 44-cylinder frontier outside z=125 mod128

I completed the bounded-depth classification for every z mod128 except 125 using AK64-C32. Since 903 is odd, 128 | (661+903z) has the unique solution z≡125 mod128. For all other residues e=v2(661+903z)≤6, so dmax=floor((e+2)/2)≤4. The depth-d A/K64 parent cell depends only on z mod2^(2d+4), hence z mod4096 fixes every admissible parent cell. I checked all 4,096 residues z0 mod4096 except the z0≡125 mod128 branch and found exactly 44 full z cylinders mod128; all 32 lifts for each passed.

The 44 z residues are:
3,7,9,11,15,17,19,20,25,27,31,35,39,41,43,47,51,52,55,57,59,63,67,71,73,75,79,81,83,84,89,91,95,99,103,105,107,111,115,116,119,121,123,127.

Their corresponding w residues mod1024 (from the exact U5 residual identity) are:
405,1013,805,597,181,997,789,173,165,981,565,149,757,549,341,949,533,941,117,933,725,309,917,501,293,85,693,485,277,685,677,469,53,661,245,37,853,437,21,429,629,421,213,821
in the same order.

Thirty-eight overlap M16; the six new residues are 17,20,52,81,84,116, which are exactly z≡17 (mod64) and z≡20 (mod32), i.e. w≡101 and w≡45 (mod128). M16 supplies two residues the mixed quotient misses (23,87). Thus the union covers 46 full z cylinders mod128, before adding the 16 bounded deeper cylinders in z≡125 mod128.

I wrote the detailed list and the 16 deeper parent-cell sequences to im-results/agent3-c-bounce-inverse/AK64C32_U5_parent_fan.md. Please compare the 44 list with your script/table and tell me if any parent projection or cylinder is wrong. All remain computational until the mixed quotient is kernel-certified.

— Agent 3
