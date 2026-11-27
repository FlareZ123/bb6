# Raw44: five-hole child reduction and two growing residual machines

Status: complete computational/paper-level argument for a single child; not Lean-accepted. No whole Raw44 or global roster cut is claimed.

Parent (canonical manifest Raw44): `1RB---_1RC---_0RD---_1LD1LB_------_------`. Here we study B1=0RC, C1=0RA, namely `1RB---_1RC0RC_0RD0RA_1LD1LB_------_------`.

Run `node discover.cjs`. The committed `0RC-0RA.json` records the result: 12,601 nodes, 525 first-hole splits, 2,096 last-hole finite-query leaves, 9,880 translated lassos, 96 sparse n-gram closures, four one-hole residuals. Mass by category: 570,525 halt-at-split; 52,400 last-hole; 9,128,200 lasso; 14,400 n-gram; 100 residual. Sum 9,765,625 = 25^5. Maximum live time to any first hole is 369. A last-hole ordinary assignment cannot halt since every slot is then ordinary. The weighted first-one convention adds at most 6 to the live time (halt query and blank delay), hence 375 suffices if all nonhalting checks are accepted.

Directional lasso justification: for an observed segment with same control state and head displacement d >= 0, let m be the minimum visited head position. Exact equality of the two tape half-lines from m and m+d, relative to the respective head positions, permits replay translated by d, indefinitely. The next required half-line lies inside the previous matched half-line; the finite segment does not read outside it. The leftward case is symmetric. Equality is checked by full one-sided BigInt stacks and a finite prefix of the other stack; d=0 also works. Sparse n-gram fixed-point search uses the same stack abstraction as agent47-raw111-cut/ngram_sparse.cpp: the head symbol is separate, every (k+1)-bit window on each stack is admitted by that side's edge relation, a push adds its new boundary window and a pop removes one. Abstract successors for all admitted pop continuations are closed, and no reached control/head pair has an undefined instruction. Initial blank stacks are admitted. A cutoff or failed closure never classifies a machine. This is a finite certificate-generation algorithm, not a kernel-checked certificate.

## Four residuals, two representatives

M1 = `1RB0LE_1RC0RC_0RD0RA_1LD1LB_0LF---_1LA1LB`
M2 = `1RB1RE_1RC0RC_0RD0RA_1LD1LB_---0RF_0RC0RE`

The other two listed in the JSON are exactly their E/F state renamings, which fix the start A. All four can be decided without guessing unbounded behavior.

Write an E configuration as (L,R), where L is nearest-first and excludes the head, R is nearest-first and includes it, and finite displayed words are zero-padded. For M1 use arbitrary infinite tails alpha,beta in the following exact E-to-E rewrites; the listed cost counts ordinary moves. The only E instruction used is E0.

| Rule | Input L prefix | Input R prefix | Output L prefix | Output R prefix | Cost |
|---|---|---|---|---|---:|
| 1 | 001 | 00 | 0 | 0011 | 12 |
| 2 | 010 | 0 | empty | 0010 | 3 |
| 3 | 11 | 0010011 | 1101100 | 00 | 11 |
| 4 | 000 | 00 | 1 | 0011 | 12 |
| 5 | 10 | 0011 | 1101 | 00 | 8 |
| 6 | 11 | 0010000 | 001100 | 001 | 16 |
| 7 | 11 | 0011 | 1100 | 00 | 8 |

Each prefix pair bounds the entire visited tape segment. The tails alpha,beta are unchanged and appended to the corresponding output prefixes. The local checker in this directory rejects any read outside the input window and checks the final window and head. No unknown transition is executed.

Define U = 01100 and V = 00. Define [k0,...,km] to be R = concatenation of blocks 00 followed by 2*k_i+1 ones, then infinite zeros. Let A(n) be L=1101 with R=[0,1^n] (n entries of value 1); B(n) be L=11011 with the same R. Let base b be 01 for A, 011 for B.

For either base, repeat rule 3 n times: (11 base,[0,1^n]) becomes (11 U^n base,[0]). Rules 6,1,2 in sequence change it to (0 U^n base,[0,1]). Each pair 1,2 removes one U from the left and inserts one value-1 block on the right. Thus after 26n+31 moves the configuration is (0 base,[0,1^(n+1)]).

For base 01, rules 1,4,5,7 in sequence yield (11 V 01,[0,1^(n+1)]). Repeat the same drain with n+1 in place of n, keeping V 01 as the base. This yields (0 V 01,[0,1^(n+2)]). Rules 4,5 produce B(n+2). The total cost from A(n) is 52n+148.

For base 011, rules 1,2,4,5 instead yield A(n+2), in 26n+66 total moves.

Blank reaches E with L all zeros, R=001 padded, at time 9. Rules 4,5 give A(0) at time 29. Consequently A(n) -> B(n+2) -> A(n+4) for every n>=0; the increasing positive-time sequence is infinite. M1 never queries E1.

For M2, blank reaches E at time 9 with L=10 and R=1, both zero-padded. At E define C(n) by L=10 1^n and R=1^(2n+1), both zero-padded. E1=0RF, F1=0RE erase n pairs, leaving E on the final 1. E1 erases this and moves right to F0; F0 then C0 move right to D0. D0 writes a contiguous block of 2n+4 ones while moving left across the blank interval, reaches D1 at the original left marker, and D1 goes left to B0. B0 writes 1 and moves right to C1, which erases the marker and moves right to A1; A1 moves right to E, leaving the first two cells of the new left stack 10 and n+1 trailing ones. The new right block has 2n+3 ones. This gives C(n)->C(n+1) in 4n+11 moves for every n>=0; only E1 is used. M2 never queries E0. (The precise count of D0 steps is 2n+4; the control/tape trace checker can independently replay instances.)

These explicit inductions settle the four exceptional tables on paper, including their ordinary and halt completions because their holes are never queried. Thus the enumerated child has a computational/paper-level weighted bound 375. This is not yet a source-checked Cover; use the repository's existing lasso and n-gram certificate machinery, and translate the two inductive return arguments to Lean. The current execution's local shell and Python runtime returned ClientError before Lean could start, so no kernel claim is made. Next target: other children of Raw44, especially the remaining C1 values under B1=0RC; use E/F symmetry before new searches.
