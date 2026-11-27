# Leaf66: exact primitive cost and stationary head at growth sections

Table `1RB0LA_1RC0RE_0RD1LC_1LD1LA_---0RF_1RA1RF` (E0 unassigned).
This refines the existing [nonhalting derivation](A0LA1LC-leaf66-normalized-drain.md).
It is a mathematical result, not yet kernel accepted. Seven unused normalized
cases can be eliminated. The head returns to the **same absolute coordinate**,
not merely an equivalent translated configuration.

## Three framed primitive computations

Use nearest-first L,R excluding the scanned cell; every displayed start and
end is A scanning 0. Untouched suffixes are arbitrary infinite binary words
of finite nonzero support, with implicit zeros. Costs count assigned
primitive moves.

| Macro | Input (left,right) | Output (left,right) | Moves | Shift |
|---|---|---|---:|---:|
| Lead, b>=3 | L, 1^b 00 R | 1^(b-1)001 L, R | b+2 | b+2 |
| Merge, k>=0 | 1^k 0 L, 01 R | L, 1^(k+3) R | k+7 | -(k+1) |
| Erase, k>=0 | 1^k 0 L, 000 R | L, 0^(k+1)111 R | k+7 | -(k+1) |

Lead: A0, B1, E1, followed by b-2 F1 moves and one F0 move. All
moves are right. Merge: A0, B0, k+3 C1 moves left, then C0 and D1.
The C1 sweep includes the two freshly written ones and the old scanned
cell, and stops on the displayed left delimiter. Erase: A0, B0, C0,
D0, D0, D1, then k+1 A1 moves left. The first six moves have zero net
displacement. These transition words prove the macros with untouched tails.

Only two composites are needed, with b>=4.

* Join: (1^k L, 1^b 000 1^c R) -> (0 1^(k+1) L, 1^(b+c+1) R),
  for c>=1. Apply Lead, then Merge with left run b-1. Cost
  (b+2)+(b+6)=2b+8, shift (b+2)-b=+2.
* Split: (1^k 0 L, 1^b 00000 R) -> (L, 1^(k+6) 0^(b-3)111 R).
  Apply Lead, Erase with left run b-1, Erase with left run 0, and
  Merge with left run k+1. Cost (b+2)+(b+6)+7+(k+8)=2b+k+23,
  shift (b+2)-b-1-(k+2)=-(k+1).

Split covers gap 5 (the emitted ones merge with the next run), gap >5
(two right tokens), and the infinite-blank suffix (three emitted ones).
Join covers gap 3. Along the proved trajectory all left gaps are 1;
all active right gaps are at least 3. The full nine-case normalized
relation and its g=1,2,4 branches are unnecessary.

## Weighted normalized drains

Use the preceding normalized notation (k,b,U,V), suppressing the left
gap 1: U is a list of positive one-run lengths, e=1, and
inc([])=[1], inc(x::U)=(x+1)::U. Pop replaces k with the old first U
element, or zero if empty. The previous standard drain uses token
(5j+3,3).

Define T_j(x) to be the exact primitive cost of that standard drain:
for j=1 input (x,6,U,[(8,3)]++S); for j>=2 input
(1,6,e^(j-2)++[x]++U,[(5j+3,3)]++S). Outputs are the same
as the existing standard drain lemma. Its cost and shift are

    T_j(x) = (2j+3)x + 80*2^j - 14j - 63
    H_j(x) = 3-x.

For j=1, Split costs x+35; the two Join operations cost 2x+20
and 2x+28. Total 5x+83; shift -(x+1)+2+2=3-x.

For j>=2, use the stage decomposition in the existing drain proof.
Initial Split+Join costs 36+22=58 and has shift zero.
At stage i=1,...,j-1 current k=0,b=6+5i, so Split costs
35+10i and shifts -1. Its following standard drain has parameter
2 for i<j-1, and x+1 at the final stage. Finally the last Join
at b=x+5j+5 costs 2x+10j+18, shift +2. Consequently

    T_j(x) = 58 + sum_{i=1}^{j-1}(35+10i)
             + sum_{i=1}^{j-2} T_i(2) + T_{j-1}(x+1)
             + 2x+10j+18.

Write T_j(x)=a_j x+d_j. Then a_1=5, a_j=a_(j-1)+2, hence
a_j=2j+3. Substitution gives

    d_1=83,
    d_j=5j^2+42j+42+d_(j-1)+sum_{i=1}^{j-2}(4i+6+d_i).

Subtract consecutive formulas: d_(j+1)=2d_j+14j+49 (j>=2;
also true at j=1 since d_2=229). Solving gives
d_j=80*2^j-14j-63. For displacement each nonfinal stage
contributes -1+H_i(2)=0 by induction; the last stage and final
Join contribute -1+H_(j-1)(x+1)+2=3-x.

The general gap drain (n>=1, 1<=r<=5, c>=2) has initial cost 58
and subsequent stage cost (35+10i)+T_i(2)=80*2^i-22. All
stages have net zero head displacement. Thus

    G_n = 58+sum_{i=1}^{n-1}(80*2^i-22)
        = 80*2^n-22n-80,
    shift = 0.

## Exact blank growth times

At X_n=(0,5n+8,e^n,[]) the five parts of the established root
recurrence have costs and shifts:

    Split at empty right suffix    10n+39    -1
    General drain G_n              G_n        0
    Split at gap 5                 10n+35    -1
    General drain G_n              G_n        0
    Join at gap 3                  10n+20    +2

Their sum is

    C_n = 160*2^n - 14n - 66,       shift = 0.

All primitive transitions used are assigned. Thus A scanning zero
at the same head position, with (01)^n nearest-first on the left and
1^(5n+8) on the right, grows to the corresponding n+1 configuration.

The existing blank replay enters X_11 after 93860 moves at absolute
head +10. Summing C_n gives the exact visit time for every n>=11:

    t_n = 160*2^n - 7n^2 - 59n - 232324.

Indeed t_11=93860 and t_(n+1)-t_n=C_n. At every such visit the
head is +10; t_12=421320. Since C_n>0 this proves arbitrarily
long assigned runs, uniformly over all E0 completions. This is
a subsequence of return times, not a claim that these are the
first visits to X_n or that there are no other A0 visits.

## Reproduction and source plan

`node check_leaf66_costs.js` executes 315 standard drains, 210
general drains, and 12 root epochs of the literal machine,
checking exact tape/state, transition count and head displacement.
The script passed in the JS runtime on 2026-11-27. These are
diagnostic finite checks; the universal claim follows from the
framed computations and induction above.

Candidate sources [Raw40A0LA1LC66Macros.lean](Raw40A0LA1LC66Macros.lean) and [Raw40A0LA1LC66Drain.lean](Raw40A0LA1LC66Drain.lean) implement the framed computations using SweepPumping and the positive normalized reachability induction, respectively. Their precise source composition and kernel acceptance remain outstanding. For the empty left/right cases,
use padded zipper equivalence or an explicit sufficient zero
frame, not equality of raw finite zipper lists with unequal
trailing zero padding. No parent coverage or canonical decrement
is claimed.
