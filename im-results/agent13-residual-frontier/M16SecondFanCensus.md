# M16 quotient census for Agent 21's second-parent fan

**Date:** 2026-11-23  
**Status:** Exact finite row-mask table kernel-checked in CI run [45227476270](https://github.com/FlareZ123/bb6/actions/runs/45227476270).

## Fan coordinates

Agent 21's exact profile for (m=512z+67) writes
[
F=519z+73=2^d q,qquad q	ext{ odd},
]
and considers even depths (n=2rle d). With
[
s=(F/2^n)mod16,
]
the parent coordinates reduce to
[
a_nequiv-2s-3pmod{16},qquad
k_nequiv s+5-3rpmod{16}.
]
All concrete parent coordinates are at least eight. The M16 quotient cell is therefore computed by applying `CCert.q` to the two canonical representatives and using `CCert.q 0` for the third coordinate.

## Exact absent-(s) table

In row (r=n/2mod16), the listed (s)-values are exactly those for which the M16 `CCert.seen` table returns false.

| (r) | Absent (s) residues | Count |
|---:|---|---:|
| 0 | 0, 4, 7, 8, 10, 12, 15 | 7 |
| 1 | 1, 5, 6, 9, 11, 13, 14 | 7 |
| 2 | 2, 6, 10, 11, 14 | 5 |
| 3 | 3, 4, 6, 7, 11, 12, 13, 15 | 8 |
| 4 | 0, 3, 4, 8, 11, 12, 14 | 7 |
| 5 | 1, 2, 5, 9, 10, 13, 15 | 7 |
| 6 | 2, 6, 7, 10, 14 | 5 |
| 7 | 0, 1, 2, 3, 7, 8, 11, 15 | 8 |
| 8 | 0, 2, 4, 7, 8, 12, 15 | 7 |
| 9 | 1, 3, 5, 6, 9, 13, 14 | 7 |
| 10 | 2, 3, 6, 10, 14 | 5 |
| 11 | 3, 4, 5, 7, 11, 12, 14, 15 | 8 |
| 12 | 0, 3, 4, 6, 8, 11, 12 | 7 |
| 13 | 1, 2, 5, 7, 9, 10, 13 | 7 |
| 14 | 2, 6, 10, 14, 15 | 5 |
| 15 | 0, 3, 7, 8, 9, 10, 11, 15 | 8 |

The 16 row masks are kernel-certified by the `rowMask_0` through `rowMask_15` lemmas and `rowMasks_exact` in [`M16SecondFanProbe.lean`](M16SecondFanProbe.lean). The table has 108 absent cells and 148 cells not excluded. The theorem `no_full_parent_row` proves that no (nmod32) class has all sixteen possible (s)-cells absent.

## Interpretation and boundary

This quotient supplies substantial systematic sub-cylinder exclusions in every row, but it does not eliminate a complete (nmod32) class. A `seen=false` cell is a sound unreachability exclusion through the source bridge. A `seen=true` cell means only that this quotient does not rule it out; it is not a proof that the concrete parent is reachable.

The valuation-level consequence for (F=2^d q) is being formalized separately in the same Lean module. No blank-root exclusion follows from this finite quotient census alone.
