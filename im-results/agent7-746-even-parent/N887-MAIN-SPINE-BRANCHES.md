# Exact n=887 odd-parent branch classes on the even spine

**Status: exact-integer branch census, aligned with the existing all-precision Hensel selectors. The dyadic-band and nested-side-branch proof is not yet formalized here.**

## 1. Main-spine depth range

For n=887, the same-scale even spine has 876 states, indexed by m=0,…,875. Under the canonical-ray identity `2*y_m+5=signedZ(887,m+1)`, its depth range is j=1,…,876.

## 2. First-tier depth Hensel residues

Direct modular evaluation of the exact signedZ formula gives the unique depth residue R_k modulo `2*3^k` for `3^(k+1) | signedZ(887,j)`:

| k | R_k | period 2·3^k |
|---:|---:|---:|
| 0 | 0 | 2 |
| 1 | 0 | 6 |
| 2 | 6 | 18 |
| 3 | 42 | 54 |
| 4 | 150 | 162 |
| 5 | 474 | 486 |
| 6 | 474 | 1,458 |
| 7 | 3,390 | 4,374 |
| 8 | 3,390 | 13,122 |
| 9 | 3,390 | 39,366 |

The exact Lean theorem `CascadeRayDepthResidue.depthResidue_iff` states the general all-precision criterion. The residue values above are its n=887 evaluations; the selector's source check remains subject to its own CI status.

## 3. Exact ResetParent band census on the spine

Enumerating every odd ResetParent exponent t from `3^(t+1) | signedZ(887,j)`, then applying the exact odd-band condition, gives exactly:

| odd exponent t | depth class j | count on 1≤j≤876 | odd-band scale k |
|---:|---|---:|---:|
| 1 | `j ≡ 0 (mod 6)` | 145 | 885 = n−2 |
| 3 | `j ≡ 42 (mod 54)` | 16 | 884 = n−3 |
| 6 | `j = 474 (mod 1458)` | 1 | 882 = n−5 |

No other t gives an odd ResetParent on the n=887 main spine. In particular:

- t=0,2,4,5 have Hensel divisibility classes, but their quotients lie in dyadic gaps rather than odd image bands;
- the first t=7,8,9 Hensel class begins at j=3,390, outside this n=887 spine.

The branch counts are 145+16+1=162, exactly the odd-parent edges leaving the main spine in the complete 1,319-state reverse cone census.

## 4. Second-tier t=1 gate

For every one of the 145 t=1 branches, the actual even parent w of its odd predecessor satisfies the exact source identity

`T_887(j)=16*signedZ(887,j)−9(12·2^887+6·887+3)=9(2w+5)`.

The second-tier Hensel residues and exact valuation census are recorded in `../agent10-cascade/TWO-TIER-DEPTH-887-RESIDUES.md`. On the relevant j range, the 17 depths with `3^4 | T` are exactly `j ≡ 6 (mod 54)`:

`6, 60, 114, 168, 222, 276, 330, 384, 438, 492, 546, 600, 654, 708, 762, 816, 870`.

The exact valuations among these are:

- `v₃(T)=4`: 60, 114, 222, 276, 384, 438, 546, 600, 708, 762, 870;
- `v₃(T)=5`: 6, 330, 492, 816;
- `v₃(T)=6`: 654;
- `v₃(T)=7`: 168.

Thus only 17 of the 145 t=1 branches can continue through a second-tier odd-parent gate. The nested Hensel selectors classify the next valuations, but exact source-band tests are still required to identify the actual parent edges.

## 5. What is now structurally reduced

The n=887 main-spine odd-parent set is no longer an opaque list of 162 edges: it is the union of three Hensel depth classes, with their exact dyadic scales. The second-tier t=1 branches are likewise restricted to one further depth class. This gives a compact arithmetic description of the top two levels of the 1,319-state cone.

The remaining proof work is to:

1. formalize the n=887 band/gap implications for t=0,1,2,3,4,5,6 and the absence of t≥7 in this finite depth range;
2. compose the T-selector with the exact source-parent equations for all 145 t=1 branches;
3. classify the nested odd/even branches at the 17 second-tier depths and the 16 t=3 plus one t=6 first-tier branches;
4. prove that every terminal side-branch state is parent-free, thereby deriving the finite closed certificate without relying on an unchecked list.

Do not infer a uniform n-family from this finite census. For larger n, the first t=7 and t=8 depth classes enter the main spine; higher Hensel digits eventually matter.

— Agent 7
