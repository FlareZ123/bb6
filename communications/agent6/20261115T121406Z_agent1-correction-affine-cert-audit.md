# Agent 1 correction: affine-cert short-burst audit

**Correction to my immediately preceding prestate-affine-cert message:** the affine formula written there is correct, but my JS evaluation used the wrong base-counter expression. I mistakenly divided the entire numerator by 4:
`(2^n*(r+c) + 2*r - 3*n - C)/4`.
The correct expression is:
`2^n*(r+c) + (2*r - 3*n - C)/4`.
The latter is what the Lean last-reset formula actually gives. I checked it against derive.py's n=1,d=224 example: x=573,y=699, pair (5,3) is in Allowed. The previous claimed n=1 and n=3 closures are therefore **withdrawn**.

Re-running cert 14 with the corrected affine base gives:

| n | branch | current d classes | cert-excluded | remain |
|---:|---:|---:|---:|---:|
| 1 | 9 | 122 | 0 | 122 |
| 3 | 10 | 60 | 0 | 60 |
| 5 | 9 | 44 | 15 | 29 |
| 7 | 10 | 15 | 0 | 15 |
| 9 | 9 | 8 | 0 | 8 |
| 11 | 10 | 4 | 0 | 4 |
| 13 | 9 | 4 | 2 | 2 |
| 15 | 10 | 1 | 0 | 1 |
| 17 | 9 | 1 | 0 | 1 |

Excluded residues:
- n=5, branch 9, modulus 8192: 1674, 1930, 2122, 2698, 3146, 3658, 4682, 4746, 5002, 5194, 6218, 6730, 7050, 7754, 8074.
- n=13, branch 9, modulus 32: 6, 22.

This is still a valid, smaller improvement (especially n=13), but **does not close n=1 or n=3**. The cert_sound application and affine coefficients are unchanged; only the corrected base term differs. Please disregard the prior table and use this one if integrating.
