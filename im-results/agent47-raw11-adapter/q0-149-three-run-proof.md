# q0-149: unbounded two-run returns for three one-hole cylinders

## Result and scope

The exact frozen frontier from run 46028015821, preserved as `q0-149-exact-frontier.json` on branch `agent5-q0-149-roster-46031826322`, contains these three entries (zero-based indices):

| index | partial table | blank seed steps |
|---|---|---:|
| 11 | `1RB1LC_1RC0LF_0LA0RD_1RA1RE_1LF1RD_---0LB` | 43 |
| 16 | `1RB1LC_1RC---_0LA0RD_1RA1RE_1LF1RD_1LC0LF` | 37 |
| 17 | `1RB1LC_1RC---_0LA0RD_1RA1RE_1LF1RD_1RC0LF` | 43 |

All three have an exact nonhalting proof for every completion of the hole. The proof below uses zero-padded words, arbitrary-tail local rules and induction, not a fit of large finite simulations. The included verifier checks all 51 local word identities and the three blank seeds; the unbounded composition follows from the algebra below. **Not yet accepted by the Lean kernel**: the repository's weighted-bound consumer should not remove these leaves until the corresponding formal Covers are accepted.

## Conventions and local rules

Use Q(L,R) where L includes the current cell, L and R are read nearest-first, and both are extended with infinite zeros. Thus finite trailing zeros may be appended/removed. A move (write w, left, q) sends Q(aX,R) to q(X,wR); a right move sends Q(aX,bY) to q(bwX,Y). Write arrows for positive-length paths through known transitions. X,Y are arbitrary tails: each row is a finite identity whose trace reads only its displayed prefixes. The numbers are exact costs for indices 11,16,17 respectively.

| rule | source | target | costs |
|---|---|---|---|
| enter | A(1X,0Y) | C(X,10Y) | 1/1/1 |
| sweep | C(1X,10Y) | C(X,101Y) | 7/5/7 |
| cross | C(0X,Y) | A(X,0Y) | 1/1/1 |
| prep | C(00X,101Y) | D(10011X,Y) | 7/7/7 |
| dpair | D(1X,11Y) | D(111X,Y) | 2/2/2 |
| evenEnd | D(1X,10Y) | D(011X,Y) | 2/2/2 |
| oddEnd | D(1X,0Y) | E(01X,Y) | 1/1/1 |
| e0 | E(0X,Y) | F(X,1Y) | 1/1/1 |
| fpair | F(11X,Y) | F(X,00Y) | 2/2/2 |
| fstop2 | F(100X,Y) | A(X,010Y) | 5/3/5 |
| fstop1 | F(10X,Y) | C(X,10Y) | 4/2/4 |
| d000 | D(0X,000Y) | A(111X,0Y) | 4/4/4 |
| d1 | D(0X,1Y) | A(11X,Y) | 1/1/1 |
| d001 | D(0X,001Y) | C(1111X,Y) | 3/3/3 |
| c1z | C(1X,0Y) | D(00X,Y) | 1/1/1 |
| c1o | C(1X,1Y) | D(10X,Y) | 1/1/1 |
| special | D(0X,111110Y) | F(111110X,1Y) | 9/9/9 |

An exact arbitrary-tail replay of each row, rejecting any inspection of X/Y or undefined entry, is in `verify-q0-149-three-run.cjs`. In particular the alternating F/B erase in machine 11 and the straight F erase in machines 16/17 have the same odd-length endpoints; no assumption about an unknown transition is used.

## General return calculus

Set
- T(x,y) = A(1^y 00 1^x, empty), y >= 1.
- S(x,b,W) = C(00 1^x, 10 1^b W).
- S[x,b,c,d] = S(x,b,0^c 1^d), with zero padding after the marker; x may be 0, in which case 00 1^x is equivalent to empty.
- An empty W means the infinite blank tail.

The left transfer, obtained from enter then n-1 sweeps, is
A(1^n X,0Y) -> C(X,10 1^(n-1)Y) for every n>=1. Hence T(x,y) -> S(x,y-1,empty).

For odd b=2m+1 and arbitrary U:
S(x,b,0U) -> S(0,x+2,0^b 1U). Call this O.
Proof: prep, dpair^m, oddEnd yield E(0 1^b 00 1^(x+2),U). Then e0, fpair^m, fstop2 yield A(1^(x+2),01 0^b 1U). The left transfer over x+2 ones gives C(empty,10 1^(x+2) 0^b 1U), as required. In particular U may be blank.

For positive even b=2m+2, prep, dpair^m, evenEnd take S(x,b,0U) to D(0 1^b 00 1^(x+2),U). Use this D section to obtain the following four rules.

* R (reduce): S[x,b,c,d] -> S[x+2,b+2,c-4,d] if c>=4. Apply d000, then the left transfer across b+3 ones. The d000 output right word is 0 followed by 0^(c-4) 1^d. This applies also at c=4, where the right runs merge.
* E (end): S[x,b,1,1] -> T(x+2,b+2), by d1.
* J (three-zero turn): S[x,b,3,d] -> S[x+2,b+3,1,d+1] for odd d>=1. Apply d001 to D(0 X,00 1^d), where X=1^b 00 1^(x+2), giving C(1111X,1^(d-1)). For d=1 apply c1z at the blank. For d>=3 apply c1o, dpair^((d-3)/2), evenEnd at the blank. Both give D(0 1^(d-1) 0 111X,empty). Apply d000 at the blank, giving A(1^(d+2) 0 111X,blank). Left transfer d+2, cross, then left transfer b+3. The resulting S word has b+3 ones, one zero, d+1 ones. 
* K (five-marker turn): S[x,b,1,5] -> S[x+2,b,4,1]. Apply special at the blank after the five ones: F(111110X,1); then fpair^2, fstop1 give C(X,1 0^5 1). Sweep b times (X begins 1^b). 

Induction on r gives R^r: S[x,b,c,d] -> S[x+2r,b+2r,c-4r,d] when 4r<=c, with zero iterations interpreted as identity. The b parity stays even. When r>0 every iteration is positive.

## Exceptional return

For every even x>=0, from S[x,2x+4,3,1]:

| rule | result |
|---|---|
| J | S[x+2,2x+7,1,2] |
| O | S[0,x+4,2x+7,3] |
| R^(x/2+1) | S[x+2,2x+6,3,3] |
| J | S[x+4,2x+9,1,4] |
| O | S[0,x+6,2x+9,5] |
| R^(x/2+2) | S[x+4,2x+10,1,5] |
| K | S[x+6,2x+10,4,1] |
| R | S[x+8,2x+12,0,1] = S(x+8,2x+13,empty) |
| O | S[0,x+10,2x+13,1] |
| R^(x/2+3) | S[x+6,2x+16,1,1] |
| E | T(x+8,2x+18) |

Every row's precondition holds: the three O inputs have odd b; all R/J/K/E inputs have positive even b; the stated exponents are nonnegative integers and do not overrun the zero run. These are exact positive returns, irrespective of the magnitudes of x.

## Infinite region

Define P(k)=T(8k,16k+2), Q(k)=T(8k+2,16k+4), k>=0. The three blank seeds are exactly Q(0), with respective costs 43,37,43. 

P(k) -> S(8k,16k+1,empty) -> S[0,8k+2,16k+1,1] by O -> S[8k,16k+2,1,1] by R^(4k) -> Q(k) by E.

Q(k) -> S(8k+2,16k+3,empty) -> S[0,8k+4,16k+3,1] by O -> S[8k,16k+4,3,1] by R^(4k) -> T(8k+8,16k+18)=P(k+1) by the exceptional return (x=8k).

Starting at Q(0), induction produces an infinite sequence of positive defined paths. Because every path reads only assigned transitions, it is also a path for every completion of the hole. This proves nonhalting for all such completions, hence the weighted bound is vacuous for any B. No assumption about the champion score or global BB(6) upper bound is needed.

## Integration

Reproduce the local witnesses and exact finite seed with Node: `node im-results/agent47-raw11-adapter/verify-q0-149-three-run.cjs`. It also instantiates the composed return scheme for 12 cycles as a sanity check (not the unbounded proof). The existing Lean arbitrary-tail checker `Agent5TailPump` and zero-padding relation `Agent5Frame150.ZEq` are natural targets for a generic formal proof. The remaining unresolved hard q0-149 leaves from the 2M-step run are indices 8 and 10; the finite-hole leaves and tree still require the existing acceptance path. Do not claim the whole q0-149 parent has been consumed.
