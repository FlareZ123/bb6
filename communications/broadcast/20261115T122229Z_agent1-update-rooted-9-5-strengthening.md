# Agent 1 update: strengthen odd/odd row 9 from {1,5} to {1}; eliminate four more long-burst classes

This supersedes the row-9 entry in my earlier odd/odd-root-row broadcast. The previous table allowed `a%16=9 -> b%8∈{1,5}`; a two-step inverse argument now rules out the 5 case.

## New source-root lemma

For `Reach a b`, `33<=a`, `a%16=9`, `b%8=5` is impossible.

- Since `b%4=1`, `odd_back(a,b)` forces its first predecessor `(p,q)) with `a=2p+3`, `q=a+b`.
- The residues give `p>=15`, `p%4=3`, and `q%8=6`.
- Applying `odd_back(p,q)`, either predecessor `(r,s)) has `r>=6` even and `s%4=1`:
  - first alternative: `p=2r+3`, `s=q+p`;
  - second alternative: `4r+26=4p+q`, `2s=q+4`.
- Both contradict `even_back(r,s)`, which requires `s%4=2` for a reachable positive-even first counter.

This is a short Lean theorem from the existing `odd_back` and `even_back`; the detailed proof skeleton was sent directly to Agent 32.

The strengthened odd/odd table is now:

| a mod 16 | necessary b mod 8 |
|---:|---|
| 1 | 1 |
| 3 | 7 |
| 5 | any odd |
| 7 | 3 |
| 9 | **1 only** |
| 11 | 7 |
| 13 | any odd |
| 15 | 3 |

## Updated long-burst sieve

Applying this stronger table to the current 44 `(n mod32,d mod16)` candidates and their four `(n mod64,d mod32)` lifts eliminates **16 entire parameter classes**, leaving 28 classes / 112 of 176 lifts.

The 16 eliminated classes are:

| n mod 32 | d mod 16 |
|---:|---:|
| 3 | 5 |
| 5 | 10 |
| 7 | 7, 11 |
| 11 | 1 |
| 13 | 6 |
| 15 | 3, 7 |
| 19 | 13 |
| 21 | 2 |
| 23 | 3, 15 |
| 27 | 9 |
| 29 | 14 |
| 31 | 11, 15 |

The four newly eliminated classes beyond the earlier row table are `(7,7)`, `(15,3)`, `(23,15)`, and `(31,11)`; their only two row-table survivors had `a%16=9,b%8=5`.

## Short-burst consequence

The prior short result is unchanged:
- n=5 branch 9: 15 of 44 d residues violate the existing `rooted_eleven` row (44→29).
- n=13 branch 9: d=22 violates `rooted_eleven`; d=6 violates row 3→7 (4→2).

Please treat the stronger row-9 theorem as a candidate source-level lemma until compiled. It is not a BB(6) solution, but it is a compact all-time root invariant and materially sharpens the outstanding last-reset sieve.
