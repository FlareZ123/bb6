# q0 all-F run and split formulas

**Status:** exact affine formulas and residue pruning along the all-F candidate branch. This is an intermediate reduction, not a proof that the full q0 inverse tree is empty.

Let
    a0 = 13*2^(23+32u) - 24u - 19,
    b0 = 2*a0 - 13,
    R0 = 2*a0 + b0 = 4*a0 - 13.

The first coordinate satisfies
    a0+3 = 13*2^(23+32u) - 8*(3u+2),
so
    v = v2(a0+3) = 3 + v2(3u+2).
The two summands have distinct 2-adic valuations because 3u+2 < 2^(20+32u).

## Repeated F candidate

After k consecutive F inverse steps,
    a_k = (a0+3)/2^k - 3,
    b_k = R0 - 2*a_k - 3*k.

These identities follow by induction from
    F(a,b) = ((a-3)/2, b+a).

For k<v, a_k is odd. While a_k is odd,
    b_k = 1 - 3*k (mod 4).
Therefore an S alternative is available exactly at
    k = 4*j + 1.

The F-only candidate reaches k=v, where a_v is even. This is a syntactic statement; root invariants may kill one of the alternative children at an earlier split.

## Exact children at a split

At k=4*j+1, put q=(a0+3)/2^k, so a_k=q-3. The two inverse alternatives are exactly
    F child = (q/2 - 3, 4*a0 - q - 10 - 3*k),
    S child = (a0 + q/2 - 3*j - 12, 2*a0 - q - 6*j - 3).

For q0, a0=5 (mod 8). Let r=v-k.

If r>=4, q is divisible by 16, and the two children reduce modulo 8 to
    F child = (5, 7-4*j),
    S child = (1-3*j, 7-6*j).

The F child passes the existing Allowed table. The S child is excluded immediately by Allowed when j is 0,1,3,5,7 (mod 8), but it survives Allowed when j is 2,4,6 (mod 8). Thus the all-F path has genuinely surviving side branches at an unbounded set of split positions; this is not a single-chain valuation argument.

If r=3, q/2=4 (mod 8) and q=0 (mod 8). The F child has residue (1,3) or (1,7) modulo 8, hence is excluded by Allowed. The S child has residue
    (5-3*j, 7-6*j) (mod 8).
For u=170, v=12 and the final split is k=9 (j=2), giving S child (7,3) modulo 8. This matches the exact path prefix F^9 S F E.

## Research consequence

There are at least two distinct valuation clocks in the q0 inverse tree:
- the FSFE family is controlled by v2(3u+5);
- the initial all-F run is controlled by v2(3u+2).

The surviving S siblings at j=2,4,6 (mod 8) need their own descendants analyzed. A plausible next approach is a finite-state transducer on the successive affine 2-adic linear forms, rather than treating q0 as one repeated FSFE block. No claim of termination or nonreachability follows from the formulas above.


## Secondary valuation on a surviving S sibling

At the split k=4j+1, the S child has
    A = a0 + q/2 - 3*j - 12,
    B = 2*a0 - q - 6*j - 3,
    R_S = 2*A+B = 4*a0 - 12*j - 27 = 1 (mod 4).

Its first-coordinate valuation parameter is
    A+3 = [q*(2^(k+1)+1) - 6*(j+4)]/2.

Let r=v2(q)=v-k. The two numerator terms have valuations r and 1+v2(j+4). Whenever r > 1+v2(j+4), there is no cancellation and
    v2(A+3) = v2(j+4).

The next all-F candidate run from (A,B) has the same exact formulas as before, but because R_S=1 (mod 4), its S-split positions are l=3 (mod 4), rather than l=1 (mod 4).

Consequences when r>=4:
- The only S siblings that survive the initial Allowed check are j=2,4,6 (mod 8).
- For j=2 or 6, v2(A+3)=1. The next F child is even. At j=2 its residue is (0,6) mod 8 and is killed by rooted_even_parity; at j=6 it is (2,2) mod 8 and the E alternative survives this first check.
- For j=4 and r>=5, v2(A+3)=3. The sibling has a three-F run before its first even state. If r=4, the two terms in A+3 can have equal valuation and cancellation must be handled separately.
- If j=12 (mod 16), then v2(j+4)>=4, so the next split at l=3 can occur; this is the first place where the side-branch recursion can continue. The new index is governed by the quotient (j+4)/16.

This identifies a nested valuation mechanism: the main F spine reads v2(a0+3), while an S sibling at split j reads v2(j+4). It is a candidate well-founded descent on split indices, but the surviving j=6 E child and the j=12 (mod 16) recursive branch are not yet closed.
