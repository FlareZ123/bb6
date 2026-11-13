# Second-tier depth selector at n=887

Status: exact-integer computation from the source formula; the general Lean selector is in `RayTwoTierDepthHensel.lean` and is still awaiting its selective CI result.

Define
```
T_n(j) = 16*signedZ(n,j) - 9*(12*2^n + 6*n + 3).
```
For the even-parent chain, `T_n(j)=9*(2*w+5)`, where w is the even parent of the t=1 odd predecessor of `ray(n,j)`. Thus higher 3-adic valuation of T is exactly the second-tier odd-parent gate on w.

For n=887, direct BigInt evaluation of the Hensel lift (testing the three digits at each step) gives the unique residues R_k modulo `2*3^k` for `3^(k+1) | T_887(j)`:

| k | R_k | period |
|---:|---:|---:|
| 0 | 0 | 2 |
| 1 | 0 | 6 |
| 2 | 6 | 18 |
| 3 | 6 | 54 |
| 4 | 6 | 162 |
| 5 | 168 | 486 |
| 6 | 168 | 1458 |
| 7 | 1626 | 4374 |
| 8 | 6000 | 13122 |
| 9 | 32244 | 39366 |

For the main ray depths `0 <= j <= 876` (even j), this yields:

- `3^4 | T`: 17 depths, exactly `j ≡ 6 (mod 54)`.
- `3^5 | T`: 6 depths, exactly `j ≡ 6 (mod 162)`.
- `3^6 | T`: 2 depths, exactly `j ≡ 168 (mod 486)`.
- `3^7 | T`: 1 depth, exactly `j ≡ 168 (mod 1458)`.
- `3^8 | T`: no depth in this range.

Therefore the exact valuation census among the 17 second-tier fork depths is:
- 11 depths with `v3(T)=4`;
- 4 depths with `v3(T)=5` (including j=6);
- 1 depth with `v3(T)=6` (j=654);
- 1 depth with `v3(T)=7` (j=168).

This explains why the finite n=887 reverse cone has a small number of deeper odd-parent branches: almost all second-tier forks stop at the first odd exponent, while only j=6,330,492,654,816,168 support higher valuation candidates. The source band inequalities must still be applied to decide which exponents actually occur; divisibility alone is not a ResetParent certificate.

The residue sequence is an empirical check of the intended general theorem `twoTierDepthResidue_iff`. Once its Lean source check passes, the table can be certified by `decide` at these finite precisions. Do not extrapolate this n=887 census to the entire n≡887 mod13122 family without a uniform depth-selector argument.
