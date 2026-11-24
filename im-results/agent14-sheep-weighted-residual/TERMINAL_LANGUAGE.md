# Exact terminal language of the two zero-residual branches

This extends the weighted-residual dossier. It classifies **prepared-state** terminal successors exactly, not the occurrence of those prepared states in the blank-root orbit.

For k >= 1 the two singular branches have even outputs 4(1+30k) and 16(1+102k). The next first-step excess is d+ck, with (d,c)=(5,135) or (19,1683). A terminal even return occurs precisely when

    3^H(d+ck)=2^H(2^B-1).

Here H=v2(d+ck), B>=1. Conversely the equation forces that exact valuation, since 3 and 2^B-1 are odd, and forces the next even return to 2^B. Every k>=1 in these families realizes the first singular edge by the generic formula. Thus arithmetic sufficiency is genuine for the prepared states.

## Exact classification

Neither type permits H=0. For H>=1 set D=2*3^(H-1). Necessarily B=Dq for a positive integer q.

* Type I: **every** H>=1 is possible. For H=1, q=16 mod 54; for H=2, q=50 mod 54. For H>=3, q is the unique residue modulo 54 satisfying q=0 mod 2 and 16*2^H*q=5 mod 27. In every case choose a positive q in that progression.
* Type II: H is possible **if and only if** H mod 80 belongs to {5,17,24,37,40,65}. For each such H, exactly one residue q mod 180 is possible. Its representative in 1..179 depends only on H mod 240, as follows.

| H mod 80 = r | H = r mod 240 | H = r+80 mod 240 | H = r+160 mod 240 |
|---:|---:|---:|---:|
| 5 | 71 | 11 | 131 |
| 17 | 17 | 137 | 77 |
| 24 | 22 | 82 | 142 |
| 37 | 47 | 167 | 107 |
| 40 | 34 | 94 | 154 |
| 65 | 161 | 101 | 41 |

For each admitted H,q, set B=Dq and

    k = (2^H*(2^B-1)/3^H - d)/c.

This k is an integer >=1 and is the unique prepared parameter for that H,B. The least B remains 32 for type I and 11502 for type II. Type-II allowed hidden lengths have asymptotic density 6/80=3/40, but this is a statement about H, not a distribution of H along the actual orbit.

## Proof

If H=0, type I is impossible mod 3; type II forces B=1 mod 6 (mod 9) and B=6 mod 10 (mod 11). If H>=1, cancellation gives 3^H | 2^B-1, hence D|B by the previously proved three-adic exponent-divisibility theorem.

For r=2 or 3, let C_H=(4^(3^(H-1))-1)/3^H. Cubing shows

    C_(H+1) = C_H + 3^H*C_H^2 + 3^(2H-1)*C_H^3.

Consequently for H>=r, C_H=C_r mod 3^r. The base constants are C_2=7 mod 9 and C_3=16 mod 27. Raising 1+3^H*C_H to q gives

    (2^(Dq)-1)/3^H = C_r*q mod 3^r

because every binomial term of order >=2 vanishes modulo 3^r after dividing out 3^H. Thus the three-adic factor of the condition on k is 7*2^H*q=19 mod 9 for type II, and 16*2^H*q=5 mod 27 for type I (H>=3). For type I the remaining mod-5 condition is B=0 mod 4, or q even. CRT supplies exactly one q mod 54. For H=1,2 direct order calculations give B=32 mod 108 and B=300 mod 324 respectively.

For type II, since B is even, 2^B=1+19*(3/2)^H mod 11 gives the following complete map from H mod 10 to B mod 10: 0->6, 4->8, 5->2, 7->4. The same condition mod 17 gives H mod 16 to B mod 8: 1->2, 5->6, 8->4. All other residues are impossible with even B. Intersecting these lists modulo lcm(10,16)=80 gives precisely the six stated hidden-length classes. In particular every allowed H>=5. With B=Dq the mod-10 condition uniquely determines q mod 5, since 3 is invertible mod 5; the mod-8 condition uniquely determines q mod 4. Combining these with the q mod 9 condition gives one q mod 180. Its periodicity in H follows from orders 6 for 2 mod 9, 4 for 3 mod 5, 2 for 3 mod 4, and the two hidden-length periods 10 and 16. Their lcm is 240. The displayed table is the resulting CRT calculation.

Conversely, these congruences ensure 2^H*(2^B-1)/3^H=d mod c, so k is an integer. It is positive: for type I H>=3, B>=4*3^(H-1)>=2H+9, so 2^H*(2^B-1)/3^H>=2^8*(8/3)^H>d+c; for H=1,2 the explicit minimum B suffices. For type II H>=5, B>=2*3^(H-1)>=2H+12 gives the lower bound 2^11*(8/3)^H>d+c. Thus k>=1, and the equality forces H exactly as above. This proves sufficiency and the uniqueness of k for each H,B.

## Verification status

* SingularTerminal.lean proves both sharp lower-bound implications for all H from the exact Diophantine equations, combining the previous low-H and LTE results. Both compile with only propext and Quot.sound.
* SingularLanguage.lean proves the necessary six-class restriction on H for type II (H>=1), also with only propext and Quot.sound.
* The full two-way language and CRT table above are a mathematical proof, with finite modular regression in check_singular_language.py; the three-adic lifting argument and full sufficiency have not yet been formalized in Lean.
* No new blank-root reachability or BB(6) bound follows.
