# Exact root-end target for the scalar reverse unit map

This note records a necessary terminal condition for a rooted reverse-unit trajectory. It is not yet a contradiction.

## 1. Last-unit predecessor

For the exact unit map
`d_j = (2 d_{j-1}) mod (q+j)`,
if the trajectory starts at `(q,d)`, has `d<q`, and satisfies `d_m=1` for `m>0), then with `Q=q+m` and `x=d_{m-1}`,
`2x mod Q = 1`.
Since `x < q+m-1 = Q-1`, we have `0 <= 2x < 2Q`. The only even integer in this range congruent to 1 modulo Q is `Q+1). Therefore
[
2d_{m-1}=q+m+1,qquad
d_{m-1}=(q+m+1)/2,
]
and the final unit bit is necessarily one. This is formalized in `RootTerminalConstraint.lean` as `BB6P1Unit.root_terminal_predecessor`.

## 2. Family-specific target

For the two restart families in `reverse_unit_renewal.md`,
`q_R+m_R=7P-n-3`, where `P=2^n`. Thus a rooted trajectory must have
[
d_{m_R-1}=(7P-n-2)/2.
]
The renewal scale is `A P`, with `A_I=3584/529` and `A_II=3584/599). Consequently the normalized target is exactly
[
rac{d_{m_R-1}}{AP}
=rac{7}{2A}-rac{n+2}{2AP}.
]
The limiting rational is `3703/7168` in family I and `4193/7168` in family II.

## 3. Final partial-block offsets

The remaining number of units after the last complete n-unit block is `m_R mod n`. The following values were computed exactly by modular exponentiation, using the family equation for `u`; they are examples, not a general theorem.

| Family | h | n | `m_R mod n` |
|---|---:|---:|---:|
| I | 0 | 5,362 | 1,201 |
| I | 1 | 600,418 | 101,959 |
| II | 0 | 9,538 | 2,807 |
| II | 1 | 712,786 | 130,123 |

Reproduction of `m_R mod n`: compute `P0 = 2^n mod (b*n)`, where `u=(aP-c)/b`; then `u0 = ((a*P0-c) mod (b*n))/b mod n`, and `m_R mod n = (14*u0-3) mod n`. The pairs `(a,b,c)` are `(17,1058,636)` and `(87,1198,712)`.

## 4. What remains open

The exact terminal target gives a boundary condition for the final partial block. The renewal theorem currently guarantees safety and phase-denominator growth only for each fixed number of complete n-unit blocks. The rooted trajectory would require roughly `m_R/n = Theta(P/n)` blocks, so the fixed-B p-adic induction cannot simply be extrapolated to the terminal block. A useful next result would relate the p-adic numerator/error term after a growing number of renewals to the exact target above.

No root-end exclusion is claimed here.

## 5. Distinguish restart cost from wall cost

The symbol `m_R=14u-2n-3` in the reverse-unit analysis is the cumulative cost of the restart state measured from the root; it is **not** the terminal wall's `CountCone` cost. The locally source-valid suffix from that restart state to the wall consists of `s=(n+2)/3` depth-two edges (cost 3 each, total `n+2`) followed by three shallow/low edges of total cost 7. Thus the terminal wall cost is
```
m_wall = m_R + (n+2) + 7 = 14u-n+6.
```
The source-wall carry wrappers use `m_wall` in the `CountCone` and wall identity. The reverse-unit terminal target in §§1–2 uses `m_R`. Confusing these two costs would make the source composition inapplicable; the PR #109 wrapper has been corrected to use `m_wall=14u-n+6`.
