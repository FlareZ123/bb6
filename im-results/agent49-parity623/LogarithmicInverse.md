# Complete logarithmic inverse for the #623 section map

Status: exact mathematical completeness bounds, locally kernel-checked arithmetic and source adapter against a definition-identical excerpt of Cryptids c86f15861709b76042998c5211c7b2f83991621b. Full original-source workflow integration added; do not report its new run as passing until observed. This is an inverse algorithm for individual section states, not a decision of the blank-root orbit.

## Inverse window

For a successful drain B(A,b,z)=D(x,y), define n=1+floor(log2(y)) (n=1 for y=0). The six flat equations imply

* |A-x| <= n;
* z+3b <= y <= z+3b+4n.

Indeed, the child block count is <2^(k-1) whenever 0<b<2^k, including the two zero-budget branches. At each successful flat step the first budget changes by at most one, and the potential z+3b increases by 0, 4, 2 or 1. Induction on the binary length proves the bounds with any n satisfying b<2^n. Applying the coarse budget b first proves z+3b<=y, hence the output-indexed budget suffices. No positivity assumption on intermediate A.

The inverse rectangle therefore has O(n^2) candidates, even for a target with exponentially many possible predecessor coordinates by a naive linear scan.

## Positive-budget injection

If x>=2n, the window forces A>=n, so no nonterminal flat step reaches A=0. Let J(b) be the signed first-counter change and E(b) the excess of the third output over 3b. Both depend only on b. Their exact recurrences are, for b>0 and q=floor(b/3), r=b mod 3,

    b' = q+r-1
    J(b) = J(b') + (1 if r=0 else -1)
    E(b) = E(b') + (0,4,2)[r]

with J(0)=E(0)=0. Write F(b)=3b+E(b). Then B(A,b,z)=D(A+J(b),z+F(b)).

**Theorem.** F is injective on naturals and F(b+2)>=F(b)+2.

Proof: E(b)<=E(b+2)+4 by strong induction. For b=3q>0, the comparison reduces to E(q-1)<=E(q+1)+4, with an additional favorable 2. For b=3q+1, E(b)=4+E(q) and E(b+2)=E(q). For b=3q+2, E(b)=2+E(q+1) and E(b+2)=4+E(q+1). The base b=0 follows from nonnegativity. Thus F grows strictly on both parities. E is even by induction, so F preserves parity, making cross-parity collisions impossible. QED.

Consequently for fixed z and a large-first target there is at most one successful pair (A,b), found by parity-specific binary search over the O(n)-wide block interval and signed subtraction A=x-J(b).

## Exhaustive parent reconstruction

For non-axis inputs the exact source map has the following reconstruction, using the bundled RE drain (the initial evalA is literally the first drainB recursion, whose decrease guard is discharged by evalA_second_le).

| Branch | z | b parity | a | d |
|---|---:|---|---|---|
| LO (far left, odd d) | 5 | even | A+b+2 | b-3 |
| LE (far left, even d) | 2 | even | A+b | b-2 |
| RO (right, odd d) | 3 | odd | b+1 | A+b-3 |
| RE (right, even d) | 0 | odd | b-1 | A+b-2 |
| diagonal a=d+2 | 2 | even | b | b-2 (A=0) |

The remaining axis case sends (0,d) to (d,7) for even d or (d-1,14) for odd d. Odd a outside the two far-left cases halts. Subtraction in the table is signed; discard negative candidates and verify each remaining candidate using the exact flat section transition. The source theorem parent_window_complete exhausts every successful original transition, including zero-budget, near-diagonal and parity exceptions.

For x>=2n, each z has at most one pair; output y odd selects LO or RE, and y even selects LE or RO. Thus there are at most two non-axis predecessors outside the small-first strip. In the small-first strip enumerate the inverse rectangle and the diagonal special case. The Python consumer is O(n log n) arithmetic operations in the large-first region and O(n^3) in the small-first region, ignoring arbitrary-precision bit costs. The reverse graph is well-founded by the source-proved strict mass increase. Fixed-target exhaustive inverse closure is now practical without scanning the target-size range, although whole infinite families still require mathematical certificates.

## Reproduction and scope

* DrainCorrectionGrowth.lean: positive trace counts, lower bound on correction magnitude, abstract exact drain inverse window, positive-budget trace existence, exact image/drift, image injection.
* InverseWindowSource.lean: instantiates those theorems against the unchanged source definitions and prior certified flat equations; parent_window_complete and source_large_first_unique.
* inverse623.py: exact integer consumer; default run checks 14,641 targets in [0,120]^2 against forward enumeration of the entire necessary parent mass simplex, both unrestricted and even-first. Passed locally. This test supports the implementation, not a replacement for the mathematical proof. The Python consumer itself is not kernel verified.

Lean 4.36.0-rc2 accepted the new modules locally (source adapter against the exact excerpt rather than a full upstream checkout); printed theorem axioms were subsets of {propext, Classical.choice, Quot.sound}. The existing manually dispatched flat-drain workflow now compiles both new modules against the pinned original source. No new global BB6 bound or source-machine nonhalting claim is made.
