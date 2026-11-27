# Raw40 A1=1LC B1=0LC: three periodic-sweep residuals

The following three one-hole tables have F0 undefined. Each admits a direct nonhalting proof for every compatible completion. This is mathematical candidate evidence; the original-source Lean audit of the enclosing five-hole cylinder is separate.

| Leaf | Literal partial table | Entry | Return cost |
|---:|---|---:|---:|
| 39 | `1RB1LC_1RC0LC_0RD1LE_1LD1LA_1RF1LF_---0RA` | 9 | 45+52n |
| 95 | `1RB1LC_1RC0LC_0RD1RE_1LD1LA_1RB0RF_---0LD` | 42 | 51+18n |
| 118 | `1RB1LC_1RC0LC_0RD1RE_1LD1LA_1RF0LD_---1RB` | 34 | 37+12n |

Notation: `(q,L,R)` is the exact zipper with scanned cell first in L (missing means blank), left suffix nearest first, and R strictly right of the head. All omitted cells are zero. P=01, Q=10, W=11, T=1111. Concatenation is juxtaposition, powers repeat words. X,Y denote arbitrary finite untouched tails. The tables below are exact finite transition identities, not fitted time formulas. They can be checked by unfolding ordinary moves; the accompanying Lean source checks them by reflexivity.

## 39

Family C(n)=(A,0,11 P^(2n) 11), entry at 9 steps.

| Cost | Source | Target |
|---:|---|---|
| 10 | (A,0,11Y) | (A,0011,Y) |
| 18 | (A,00X,01Y) | (A,0011X,Y) |
| 10 | (A,00X,11) | (A,0011X,empty) |
| 9 | (A,00X,empty) | (A,0X,1111) |
| 8 | (A,011X,11Y) | (A,0X,1101Y) |

Apply first, repeat second 2n times, apply third and fourth, then repeat fifth (2n+2) times. Just before the final sweep the left word is 0 W^(2n+2), right 1111; the final sweep produces 11 P^(2n+2) 11. Thus C(n)->C(n+1) in 10+36n+10+9+8(2n+2)=45+52n moves.

## 95

Family C(n)=(A,0,111 P^(2n+2) 1), entry at 42 steps.

| Cost | Source | Target |
|---:|---|---|
| 10 | (A,0,1110Y) | (B,01111,Y) |
| 6 | (B,0X,1010Y) | (B,01111X,Y) |
| 14 | (B,0X,1011) | (A,11111X,111) |
| 6 | (A,111X,1Y) | (A,1X,110Y) |
| 3 | (A,1,1Y) | (A,0,11Y) |

The first rule leaves right T'^(n)1011 where T'=1010. Repeat second n times, then third. The left is now 1 W^(2n+4), right 111. Apply fourth 2n+4 times, then fifth: resulting right 11 Q^(2n+4) 11 = 111 P^(2n+4) 1 by rotation. Total 10+6n+14+6(2n+4)+3=51+18n.

## 118

Family C(n)=(A,0,11 P^(2n+2) 11), entry at 34 steps.

| Cost | Source | Target |
|---:|---|---|
| 5 | (A,0,110Y) | (B,0111,Y) |
| 4 | (B,0X,1010Y) | (B,01111X,Y) |
| 13 | (B,0111X,10111) | (A,111111111X,111) |
| 4 | (A,111X,Y) | (A,1X,10Y) |
| 3 | (A,1,Y) | (A,0,1Y) |

The first rule leaves right (1010)^n10111; repeat second n times. Third applies because all the left tail after the head consists of ones and contains at least the fixed three ones. Its output is 1 W^(2n+4) on the left, right 111. Repeat fourth 2n+4 times, then fifth. The right result 1 Q^(2n+4)111 equals 11 P^(2n+4)11. Total 5+4n+13+4(2n+4)+3=37+12n.

## Consequence

In every case, induction on n using the displayed local identities yields arbitrarily long ordinary live prefixes from blank. None of the identities reads F0. Every compatible completion agrees on each prefix, so no completion halts. Together with 105 FAR and 14 compact invariant candidates, this covers all 122 open representatives of the A1=1LC B1=0LC five-hole child at candidate weighted bound 106 (attainment after 105 ordinary steps, zero blank delay). See `a1lc-0LC-discovery.json`. No aggregate acceptance yet.
