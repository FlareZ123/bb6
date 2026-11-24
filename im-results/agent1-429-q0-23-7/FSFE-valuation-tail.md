# q0 FSFE valuation tail and competing inverse branch

**Status:** exact algebraic reduction of one inverse branch, plus a partial analysis of its competing sibling. This is not a q0 nonreachability theorem and does not decide #429 or BB(6). It complements [FSFE-2adic-block.md](FSFE-2adic-block.md) and [Q0ResidueCoverage.md](Q0ResidueCoverage.md).

## Coordinates and exact block

Use
    w = z+1 = b-a-8,     R = 2a+b.

The q0 target has
    a = 13*2^(23+32u) - 24u - 19,
    b = 2a - 13,
    w = 13*2^(23+32u) - 8(3u+5).

Since 3u+5 < 2^(20+32u), the two terms in w have distinct 2-adic orders, and
    v2(w) = 3 + v2(3u+5).

For a block-start state (a,b), write b=a+w+8. Under
    a >= 29,  a = 1 (mod 4),  16 | w,  w >= 16,
the F,S,F,E inverse branch has exact intermediate states
    P1 = ((a-3)/2,          2*a + w + 8)
    P2 = (a + w/4 - 6,      a + w/2 + 6)
    P3 = ((a-9)/2 + w/8,    2*a + 3*w/4)
    P4 = (a + 5*w/16 - 8,   a + 3*w/8).

The first three inverse choices are legal; P3 has positive even first coordinate. Its second coordinate satisfies
    P3.second = 2 (mod 8)  iff  v2(w) >= 5.
Thus the all-time positive-even-eight root invariant permits completion of this block exactly when v2(w)>=5. At the endpoint,
    w' = P4.second - P4.first - 8 = w/16,
    R' = 2*P4.first + P4.second = R - 24.

If v=v2(w0)=3+k, where k=v2(3u+5), the number of completed blocks along this branch is
    m = floor((v-1)/4) = floor((k+2)/4),
leaving residual valuation v-4m in {1,2,3,4}. This counts completed F,S,F,E blocks only. It does not dispose of the remaining F/S alternatives or the final partial inverse tree.

For every non-final completed block the current w is divisible by 256. Hence
    a' = a + 5*w/16 - 8 = a - 8 (mod 16).
On the q0 subfamily u=9 (mod 16), the initial a=5 (mod 16), so block-start residues alternate 5,13,5,13,... modulo 16 while the non-final block condition holds.

## Competing F sibling: corrected exact all-F formulas

The prior version of this section contained an arithmetic error. It gave the second coordinates after three and four consecutive F inverses as 3a+w+2 and (25a+8w-5)/8. Both are incorrect. The derived mod-128/mod-256 sibling table and its claimed exclusions are withdrawn.

For any block-start state (a,a+w+8), set R=3a+w+8. The exact all-F run (while integral and legal) is

    a_k = (a+3)/2^k - 3
    b_k = R - 2a_k - 3k.

In particular the competing F child after the first F (instead of S), and the next two F children, are

    F^2 = ((a-9)/4,  (5a+2w+13)/2)
    F^3 = ((a-21)/8, (11a+4w+17)/4)
    F^4 = ((a-45)/16,(23a+8w+13)/8).

The incorrect formula for F^3 had added the wrong first coordinate. Its consequences for parity and later branches are not valid.

For the q0 initial state, after j completed FSFE blocks,

    w_j = w0/16^j
    a_j = ((4*16^j-1)/3)*w_j + 21 - 8j.

The coefficient C_j=(4*16^j-1)/3 is an odd integer, and

    a_j+3 = C_j*w_j + 8(3-j).

When 256 divides w_j, write a_j=21-8j+256A and w_j=256W. Then the competing F^2 child is (3-2j+64A,59-20j+640A+256W). The subsequent F^3 child is (-j+32A,62-22j+704A+256W). The first child's second coordinate is 3 mod 4, so its next F is forced if it survives. For j=1 mod 4 the F^2 child violates Allowed; for j=0 mod 4 the F^3 child is even with second coordinate 6 mod 8 and cannot be rooted. For j=2 mod 4, F^3 is even with second coordinate 2 mod 8, so E remains a candidate. For j=3 mod 4, F^3 is odd with second coordinate 0 mod 4, so F remains a candidate. Further existing predicates can prune some cases; none of these observations proves full branch closure.

## Fixed-index secondary spine: a rigorous obstruction

At j=3 the additive term in a_j+3 vanishes identically:

    a_3+3 = 5461*w_3.

The new [Q0SecondarySpine theorem](Q0SecondarySpine.md) proves that for **every** natural K some genuine q0 parameter admits the inverse word (FSFE)^3 F^K, with all edge guards and all the residue predicates in Agent 6's depth-16 sieve satisfied at every vertex. This is a Lean-checked all-depth arithmetic model. The branch is synthetic, so it does not establish actual blank-root ancestry. It rules out closing the q0 tree by a uniform cap on all-F suffix depth after compressing only the FSFE blocks.

The previous mod-256 sibling exclusions are superseded by these corrected formulas. Remaining work: characterize all F/S/E siblings and terminal tails or find a new history-sensitive invariant that excludes genuine root ancestry. The FSFE valuation identity itself and the root-compatible completed-block formula earlier in this note are unchanged.
