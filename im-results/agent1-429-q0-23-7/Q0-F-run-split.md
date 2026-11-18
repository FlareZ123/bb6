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
- If j=12 (mod 16) and r>=5, then v2(A+3)>=4, so the next split at l=3 can occur. If r=4, then v2(A+3)=3 and the first coordinate is already even after three F steps. The exact parameter transformation at the l=3 split remains to be derived.

This identifies a nested valuation mechanism: the main F spine reads v2(a0+3), while an S sibling at split j reads v2(j+4). It is a candidate well-founded descent on split indices, but the surviving j=6 E child and the j=12 (mod 16) recursive branch are not yet closed.


## Partial closure and nested side-branch cases

The uniform result is the j=2 (mod 8) sector: its S child is (3,3) mod 8, and its F parent is positive even (0,6) mod 8, excluded by rooted_even_parity.

The other two surviving sectors require more care; the following calculations close only selected representatives and expose a nested branch.

**j=6 exactly.** The S child is (7,3) mod 8. F gives a positive-even (2,2) state, so E is forced. Here k=25. Write q=2^r*t with t odd. The E child is exactly
    A2 = ((10*2^k + 1)*q - 328)/8,
    B2 = ((6*2^k - 1)*q - 156)/4.
Modulo 8 it is (1 or 5, 5) for r=4, (3,1) for r=5, and (7,1) for r>=6. Thus the j=6 representative is excluded by Allowed for r>=6; only r=4,5 remain.

For general j=8*s+6, the same E child is
    A2 = ((10*2^k + 1)*q - 30*j - 148)/8,
    B2 = ((6*2^k - 1)*q - 18*j - 48)/4.
For r>=6 this reduces modulo 8 to
    (A2,B2) = (-6*s-1, -4*s+1) (mod 8).
This is killed by Allowed when s=0 (mod 4), but can survive for s=1,2,3 (mod 4). Hence the j=6 calculation does not close the whole j=6 (mod 8) sector.

**j=4 exactly.** Put A=a0+q/2-24 for its S child. Then
    A+3 = [q*(2^(k+1)+1)-48]/2.
If r>=5, v2(A+3)=3. After three F steps the first coordinate is even and the second is 0 mod 4, so the branch is impossible. If r=4, write q=16*t with t odd; then
    (A+3)/8 = t*(2^(k+1)+1)-3
is even. After three F steps an odd state with second coordinate 2 mod 4 remains, and another S split is available.

For general j=8*s+4, the same formula gives
    A+3 = [q*(2^(k+1)+1)-48*(s+1)]/2.
If r>4+v2(s+1), then v2(A+3)=3+v2(s+1). In particular, when s is even and r>=5, the branch has a three-F run and then dies; when s is odd and the valuation is sufficiently large, the three-F run ends at another S split. This is a nested branch, not a closed sector.

The correct conclusion is therefore limited: the j=2 (mod 8) siblings close uniformly; the j=4 and j=6 sectors contain nested residue-dependent branches. The exact j=4 and j=6 calculations above are useful terminal reductions but do not bound all earlier side branches. The main-spine terminal cases r=1,2,3,4 also remain separate obligations.


## Exact parameter forms after the surviving macros

These formulas expose the next 2-adic linear forms but do not by themselves close the recursion.

For j=8*s+6, after the S child and its forced F,E pair, the resulting first coordinate A2 satisfies
    A2+3 = [(10*2^k+1)*q - 16*(15*s+19)]/8.
Thus, when the two terms have distinct valuations,
    v2(A2+3) = min(r, 4+v2(15*s+19)) - 3.
The resulting rank is R_S-10, which is 3 mod 4, so its next F-run splits at l=1 mod 4.

For j=8*s+4, when the S child reaches its l=3 split and takes S, the new state (A2,B2) is exactly
    A2 = (A+4*R_S-161)/16,
    B2 = (4*R_S-A+1)/8,
and
    A2+3 = [q*(34*2^k+1) - 16*(51*s+61)]/32.
When the two terms have distinct valuations,
    v2(A2+3) = min(r, 4+v2(51*s+61)) - 5.
The resulting rank is R_S-20, still 1 mod 4, so its next F-run splits at l=3 mod 4.

The appearance of 15*s+19 and 51*s+61 suggests a recursive affine 2-adic transducer on the split index. This is a research lead only: the exceptional equal-valuation cases, root-invariant pruning at the next split, and well-foundedness of the resulting index transformations remain open.
