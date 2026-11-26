# Root53: exact binary-counter nonhalting leaf

**Status.** Complete unbounded nonhalting proof in the independent infinite-tape Lean model: [`Root53.lean`](Root53.lean), checked with Lean 4.36.0-rc2; `Root53.validProgress` and `Root53.never` depend only on `propext`, `Quot.sound`. The exact 11-step seed, arbitrary-length sweeps, carry cases and invariant preservation are kernel checked. [`Agent5Root53Counter.v`](Agent5Root53Counter.v) is the original-source port, pending Rocq acceptance; [`q0-root53.cjs`](q0-root53.cjs) generates the exhaustive parent proof with a symbolic leaf and 40 FAR leaves. Independent finite tests are in root53-counter.py. This is not yet a source-accepted parent Cover.

Root53 full generator executed against repository JavaScript and exact q0 export: 30,793 nodes; 18,227 side, 5,664 coarse pair, 1,283 split, 5,578 last-hole, 40 FAR, 1 symbolic; maximum first-hole trace 202; weighted candidate bound 208. All 40 totalized DFA MITM checks passed; generated 24 proof shards, symbolic leaf in S22. No original-source kernel acceptance yet.

Machine (E0 undefined):
```
1RB1RD_1RC1RE_0LA0RC_1LA1LD_---1LF_1LC0LE
```

Write configurations from left to right, with the current scanned symbol inside the state marker, and implicit zero padding at both ends. Write powers for repetitions of words.

## Main section and counter encoding

Define S(P,n) = P 1^(2n+1) [B1] 111, where n>=0. The finite prefix P is empty or ends in 0; use implicit zeros when P is empty. For q>=0 and phase p in {0,1,2}, define P(q,p):

- q=0: P(0,0)=empty, P(0,1)=110, P(0,2)=100.
- q>0: let b1...bk be its ordinary binary expansion, b1=1. Start with header 110. For each adjacent pair of bits append the block f(bi,b(i+1)), with f(0,0)=00000, f(0,1)=00110, f(1,0)=11000, f(1,1)=11110.
- For p=0 or 1 append the terminal block f(bk,p). For p=2 append 00100 if bk=0, or 11100 if bk=1.

**Return theorem.** For all q,p,n as above, the exact primitive dynamics maps S(P(q,p),n) by a nonempty finite sequence of defined transitions to S(P(q,p+1),n+1) if p<2, and to S(P(q+1,0),n+1) if p=2. The proof uses no finite cutoff and the parameters q and n are independent.

## Primitive macro rules

1. **E/F sweep.** From P 1^(2n+1) [B1] 1R, B1 moves right to E1, then E1 moves left to F1. Successive F1/E1 steps replace alternating ones with zeros, moving left. Since the left run has odd length, the final E scans the leftmost 1, then F scans the zero immediately preceding it. F0 writes 1 and moves left into C. The C head is now one cell left of the final zero of P, with right word 11(01)^(n+1)R. All E visits read 1. For P empty use zero padding.

2. **C scan.** On a run 1^r0 (r>=1), C1 erases the r ones while moving right, C0 moves left to the last erased cell, A0 writes 1 and moves right to B0, which writes 1 and moves right to C. Net replacement 1^r0 -> 0^(r-1)11, C on the next cell. If C reads 0 and its left neighbor is 0, the C0/A0/B0 steps replace the pair of zeros by 11 and put C immediately to their right.

3. **D fill.** If C reads 0 with left neighbor 1, C0/A1/D0 enters a leftward fill. D1 moves left across ones; D0 writes 1 and moves left to A. If A reads 1, A1 returns right to D1 and the leftward fill continues; if A reads 0, A0 writes 1 and moves right to B1. Thus the fill stops at the first pair of adjacent zeros encountered scanning left, fills both and all cells up to the original C0 site with ones, and places B on the right cell of that pair. Every intermediate transition is defined. A double-zero pair necessarily exists in the left blank padding.

## Ordinary returns

For U empty, U=V10, or U=V000 define g(U) respectively as 110, V00, or V110 (V may be empty).

Apply the E/F sweep with R=11. If P=V10, C starts on the last 1 of P, processes the initial run of three ones and a zero to 0011. If P=V000 (or empty), C starts on a zero preceded by zero, writes 11 by the second C rule, then processes the initial two ones and a zero to 011. Thus in each case the prefix output is g(P), followed by a pair of ones. The remaining input is 1(01)^n11 with trailing blanks. The n successive 10 runs each give 11; the last 1110 gives 0011. On the next blank, C0 with preceding 1 triggers the D fill, which fills the next zero and the two-zero barrier just produced. B returns with 2n+3 ones on its left and exactly three on its right. The resulting configuration is S(g(P),n+1).

For q=0, g(empty)=110 and g(110)=100. For q>0 at phase0 the terminal block is 11000 or 00000 and g changes it to 11110 or 00110. At phase1 g changes those to 11100 or 00100. These are exactly the p<2 returns.

## Carry return

For phase2, split P as U00 T00, where T begins and ends in 1, contains no 00, and U ends in 0 or is empty (allow the left padding zeros to supply this split). The first E/F sweep puts C on the second-last zero, with left neighbor the final 1 of T. By the D fill, the next B1 is at the right zero of the barrier immediately before T. There is exactly one 1 on its left since U ends in zero or padding. Its right word is 1^(t+3)(01)^(n+1)11 where t=|T| (filled T, the initial C0, and the first two ones of the earlier C right word). This carry B1 is safe.

Apply the E/F sweep again with left run length 1. C now sees right word 11(01)1^(t+2)(01)^(n+1)11. In all cases below U is empty, ends 10, or ends 000, so the same initial C rules output g(U) and 11. The next input run has t+3 ones followed by zero, and becomes 0^(t+2)11. The remaining n alternating runs and final 1110 are processed exactly as in the ordinary return. Hence the main section is S(g(U) 11 0^(t+2),n+1).

It remains to identify the prefix algebraically, which avoids relying on any empirical guess about carry patterns.

- q=0: P=100, U empty and T=1 using blank padding. Thus t=1 and the new prefix is 110 11000 = P(1,0).
- q>0 ending in bit 0: the terminal block is 00100, so U is the header and all earlier blocks, T=1. Its last ordinary block is f(b,0), ending in at least three zeros; g changes it to f(b,1). Appending 11000 encodes the final bit changed to 1. This is P(q+1,0).
- q has a zero before its trailing j>=1 ones. Choose the last such zero. The suffix of the block encoding is 00110 (11110)^(j-1) 11100. The barrier uses the leading 00 of 00110; U contains exactly the header and earlier blocks, ending in f(b,0) because the first bit is 1. T = 110 (11110)^(j-1) 111 has length 5j+1 and no 00. Then g(U) changes its terminal f(b,0) to f(b,1), and 11 0^(5j+3) = 11000 (00000)^j. This is precisely incrementing the binary integer at the last zero, with all trailing ones becoming zeros.
- q consists of j>=1 ones: P=110 (11110)^(j-1) 11100. U empty, barrier in blank padding, T=110 (11110)^(j-1) 111 of length 5j+1. The new prefix 110 11000 (00000)^j encodes binary 1 followed by j zeros.

This exhausts phase2 and proves the return theorem.

## Blank seed and nonhalting

The blank-start first eleven ordinary transitions are
```
[A0]
1[B0]
11[C0]
1[A1]
11[D0]
1[A1]1
11[D1]
1[D1]1
[D1]11
[D0]111
[A0]1111
1[B1]111
```
with implicit zeros. The last configuration is S(P(0,0),0). Iterate the return theorem indefinitely. Each return consists of a positive number of defined transitions; therefore E0 is never reached. This proves nonhalting of the partial machine and all its completions, in the ordinary deterministic blank-start semantics. Original-source formalization is still required for a source-accepted result.

## Reproduction and scope

root53-counter.py independently replays 9,216 arbitrary triples (q,p,n), including q in 0..511 and n independently chosen from 0,1,2,5,13,37; all predicted returns agree and there is exactly one intermediate carry B1 in phase2. This finite test is a cross-check, not the proof. The local root53 exhaustive candidate tree has 30,793 nodes, 41 initially open leaves, 40 primitive finite FAR candidates; this proof addresses the remaining leaf. The parent tree, local certificates and source consumer are not yet accepted.
