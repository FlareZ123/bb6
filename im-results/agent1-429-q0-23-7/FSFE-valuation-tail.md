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

## Competing F sibling at the S split

At a block start (a,a+w+8), after the first F, the competing F parent at the next odd split is
    Q1 = ((a-9)/4, (5*a + 2*w + 13)/2).

When 16 divides w:
- If a=1 (mod 8), Q1 is positive even and its second coordinate is 1 (mod 4), contradicting rooted_even_parity.
- If a=5 (mod 8), Q1 is odd with second coordinate 3 (mod 4), so F is forced. The next parent is
      Q2 = ((a-21)/8, 3*a + w + 2).
  If a=5 (mod 16), Q2 is positive even with second coordinate 1 (mod 4), again impossible.
- The difficult case is a=13 (mod 16). Q2 is then odd with second coordinate 1 (mod 4), so another F is forced:
      Q3 = ((a-45)/16, (25*a + 8*w - 5)/8).

For a non-final block, 256 divides w. In the difficult case a=13 (mod 16), the following residue table is exact:

| a mod 128 | Q3 modulo 8 | Consequence |
|---:|:---:|---|
| 13 | even first, second 0 | excluded by rooted-even-parity |
| 29 | (7,2) | both alternatives need further work |
| 61 | (1,6) | excluded by rooted-not-1-6 |
| 93 | (3,2) | both alternatives need further work |
| 125 | (5,6) | excluded by rooted-not-5-6 |

For the two remaining rows, the next inverse alternatives are:

**If a=29+128s:**
    F(Q3) = (-2+4s, 89+408s+w),
    S(Q3) = (15+108s+w/4, 47+200s+w/2).

The F child is positive even with second coordinate 1 (mod 4), hence impossible. The S child is (7,7) mod 8 when s is even, hence impossible by rooted-not-7-7. The case s odd survives these particular invariants.

**If a=93+128s:**
    F(Q3) = (4s, 293+408s+w),
    S(Q3) = (69+108s+w/4, 147+200s+w/2).

The F child is positive even with second coordinate 1 (mod 4), hence impossible. The S child has residue (5,3) mod 8 for even s, or (1,3) mod 8 for odd s. Allowed excludes (1,3), so only even s survives this check.

The displayed exclusions use the existing all-time root invariants rooted_even_parity, rooted_not_1_6, rooted_not_5_6, and rooted_not_7_7. The latter three are in im-results/agent39-429-1021/BB429RootMod16.lean; the four-sector calculations above are not yet a Lean theorem.

## What this isolates

The repeated FSFE path has a clean 2-adic valuation clock: every completed block consumes exactly four powers of two from w, and the endpoint rank drops by 24. The competing F sibling is immediately excluded on every block-start residue a=5 (mod 16), but the a=13 (mod 16) sibling has further surviving residue branches. Therefore the valuation calculation alone is insufficient.

The next mathematically discriminating task is to close the two surviving sibling cylinders a=29,93 (mod 128) under the full inverse grammar, or find a stronger source-root invariant that eliminates them. Separately, the residual valuations 1,2,3,4 require an exact terminal-tail table. Do not promote the repeated FSFE branch to a proof of nonreachability until every sibling and terminal tail is closed.
