# Raw139 E0=1LB, C1=0RA, leaf 286: nonhalting by a growing binary counter

Status: mathematical proof; source-level Lean integration pending. This is the only open single-hole leaf in Agent 3's residual roster blob 992b848fa8038a9ca5ff6fdd461dee0f599eeaec (source run 45935487905). Table:
`1RB0RF_1RC0RD_1LD0RA_---0LE_1LB1RC_0LE1RC`.
Codes [7,21,11,13,14,1,24,16,6,11,16,11]. The argument avoids D0 for every completion.

## Local rules

Write L B R for B scanning the first bit of R, with L in physical left-to-right order. All undisplayed tails are unchanged; blank extensions are zero. For either bit a, direct substitution of the known transitions gives:
- L a B 11 R -> L B a10 R (3 steps).
- L B010 R -> L101 B R (3).
- L a01 B00 R -> L B a1011 R (7).
- L B0110 R -> L1 B010 R (5).
- L B011110 R -> L100101 B R (6).

The first, second, third rules composed in order second/third/first give L a B01000 R -> L B a10011 R (13). Define g(k)=0^k11, P=g(2), Q=g(1)g(0), O=g(3), H=g(1), X=1011, M=01 P 11. If B scans the last 1 of a block 0 1^r (r>=1) with strictly-right tape 1 P W, the first rule r times followed by the 13-step turn reaches B immediately before that block with strictly-right tape 1 P g(r-1) W. Cost 3r+13. Indeed after the r moves the head scans the separator with right word 0 1 0^(r+2)11W. This is the left sweep.

## Anchor transitions

Remaining data are groups P^x followed by Q or O, then a terminal counter P^k H^b (b=0,1), value t=2k+b. The anchor is L B M V. Let tau perform a borrow on the remaining separator bits (Q=0,O=1, low bit first): change initial Qs to O, first O to Q, and preserve the remaining suffix. P factors are unchanged. If there is no O, change every Q to O and increment t (append H if even, replace H by P if odd).

1. L B M P W -> L X B M tau(W).
   Rules 2,5,4 (14 steps) first give L D B01 W, where D=1011001011 = X 00 1 0 11. The right scan of P uses rules 2,4 (8 steps) and appends X to the left; the right scan of Q uses 2,1,1,2,4 (17) and appends 1X. Both restore B01 at the next data. Scan until first O or the terminal end. If the scanned factors append Y, write each factor as 1^alpha 0 11, alpha=1 for P and 2 for Q. The runs after the double zero in D Y are 1, 2+alpha_1, ..., 2+alpha_s, 2. At the first O, the 13-step turn lands on the last bit of D Y, with strictly-right tape 1P g(0) W' (W' after O). Sweep the final run of length 2, producing g(1)g(0)=Q, then sweep each preceding run (P gives g(2), Q gives g(3)=O), then the initial run 1, which contributes g(0) to complete M. This leaves L X unchanged and restores the anchor at the first of D's double zero. If no O occurs and the terminal counter ends without H, the turn occurs at B01 on blank extension and produces strictly-right 1P followed by blanks; the final run 2 contributes H. If H occurs, rules 2,1,1 (9) consume H and append 1 before the turn, so the final run is 3 and contributes P. This proves tau including terminal increment.
2. L B M O W -> L X0 B M W (19 steps, rules 2,5,3,1).
3. L B M H on blank extension -> L X B M on blank extension (44 steps). Rules 2,5,1,1 (15) yield L X 00 1 B01 blank; turn 13 then sweep run 1 (16).
4. L B M on blank extension -> next row. Rules 2,5,3,1 (19) yield L X0 B01 P on blank; scan P (8), then turn (13), landing on the last bit of L X0 X with strictly-right 1P blank. Suppose L consists of X^x1(X0)...X^xm(X0)X^t, with all tape to its left blank. In L X0 X the positive runs are 1,3^x1,2,1,3^x2,2,1,...,3^xm,2,1,3^t,2,1,2 (here 3^x denotes x copies of run length 3), separated by single zeros, first preceded by blank zero. Sweep all these runs. The resulting head is two cells left of the original row's starting head, with all left tape blank and right word M P^x1 Q ... P^xm Q P^t Q H.

## Induction

S(x1,...,xm) denotes B with all left cells blank and right word M P^x1 Q ... P^xm Q H, zero extension. The blank run reaches S(5) after 928 primitive steps, head -10 (origin 0). This finite seed can be checked directly.

For s remaining separators define v as their binary value, low bit first, and N=2^s t-v. Applying tau increments N by 1 (including the borrow underflow). Consuming each P therefore increments N. When the next separator O is consumed, its low bit is 1 and N is odd; removing that separator changes N to (N+1)/2. Initially s=m, v=0, t=1 and N=2^m. Write N=2^s+a; start a=0. If group x is consumed, its separator is O precisely if a+x is odd, and after removing it the new a=(a+x+1)/2. Take x1=5 and xi=i+2 for i>=2. The first a is 3; after group i>=2 it is i+2. Thus all separators can be consumed and the terminal counter is t=m+3. With no separators, consuming a P decreases t by 2 then tau increments it by 1; consuming the final H at t=1 decreases it by 1. Each terminal operation appends X. The empty-anchor transition now yields S(x1,...,xm,m+3), with the same invariant and head shifted left by 2. Each row takes a positive finite number of steps and avoids D0. By induction the blank run has arbitrarily long defined prefixes, hence no completion can halt.

## Discovery context

Cross-parent periodic-abstraction pilot: Agent25's periodic-word BiDFA (symmetric, periods 1,2,4, k=12,16,20,24,28,32,40,48, c,m=1..3, cap=30000) failed in 71/72 cases and hit the cap once. Agent19's lag-XOR push method implemented on the same JS closure (392 symmetric attempts, cap 30000) gave 276 failures and 116 caps. These are bounded negative search results only. Primitive simulation and B-return grouping exposed the five rules above. The proof uses those local identities and the counter induction, not a simulation cutoff.
