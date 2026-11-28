# Raw44: five-hole child reductions and exact blank-root growth proofs

**Current scope:** Within Raw44 B1=0RC, **18 of the 25 C1 actions are source-certified**: five complete five-hole `Cover` theorems (C1=0LA, 0RA, 0RE, 0RF and 1RA) plus thirteen translated-cycle nonhalting children. They are pairwise disjoint and cover **175,781,250 of 244,140,625** complete machines in the B1=0RC branch (72%). The four Agent16 Covers have weighted bounds 126, 375, 211 and 211; the separate Agent8 C1=1RA Cover has bound 211. See the [consolidated Raw44 frontier result](../../results/2026-11-28-raw44-b1rc-18-c1-children-agent16-agent8.md). The search generators are untrusted; the emitted finite trees, n-gram certificates and symbolic growth proofs were checked against the original source in Lean CI. **The full seven-hole Raw44 parent remains open; no global BB(6) bound is claimed.**

Parent (canonical manifest Raw44): `1RB---_1RC---_0RD---_1LD1LB_------_------`. Here we study B1=0RC, C1=0RA, namely `1RB---_1RC0RC_0RD0RA_1LD1LB_------_------`.

Run `node discover.cjs`. The committed `0RC-0RA.json` records the result: 12,601 nodes, 525 first-hole splits, 2,096 last-hole finite-query leaves, 9,880 translated lassos, 96 sparse n-gram closures, four one-hole residuals. Mass by category: 570,525 halt-at-split; 52,400 last-hole; 9,128,200 lasso; 14,400 n-gram; 100 residual. Sum 9,765,625 = 25^5. Maximum live time to any first hole is 369. A last-hole ordinary assignment cannot halt since every slot is then ordinary. The weighted first-one convention adds at most 6 to the live time (halt query and blank delay). The complete original-source child Cover at bound 375 was accepted by [CI 46107243916](https://github.com/FlareZ123/bb6/actions/runs/46107243916).

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

These explicit inductions settle the four exceptional tables, including all ordinary and halt completions because their holes are never queried. The four growth modules were individually source-accepted (M1: [46106975907](https://github.com/FlareZ123/bb6/actions/runs/46106975907), M1Swap: [46106979259](https://github.com/FlareZ123/bb6/actions/runs/46106979259), M2: [46106710160](https://github.com/FlareZ123/bb6/actions/runs/46106710160), M2Swap: [46106713615](https://github.com/FlareZ123/bb6/actions/runs/46106713615)). The complete 12,601-node first-hole tree, all 96 n-gram closures and the four symbolic residuals were assembled into the original-source theorem `Cover (WeightedBound 375) parent` in [CI 46107243916](https://github.com/FlareZ123/bb6/actions/runs/46107243916). The JavaScript search is not trusted: the emitted `zipCheck` tree and certificate witnesses are checked by Lean. The full Raw44 parent remains open.

## Additional B1=0RC, C1=0LA child

The exact first-hole partition in [0RC-0LA.json](0RC-0LA.json) has 18,841 nodes, maximal first query time 120, and two E/F-conjugate residual tables of mass 25 each. The blank-root recurrence is `T(n) -> T(n+1)` in `16n+23` moves from entry time 12. Both representative and conjugate growth modules passed original-source CI ([M3 46106387271](https://github.com/FlareZ123/bb6/actions/runs/46106387271), [M3Swap 46106454402](https://github.com/FlareZ123/bb6/actions/runs/46106454402)); the complete generated first-hole tree and both residual proofs were assembled as `Cover (WeightedBound 126) parent` in [CI 46107124798](https://github.com/FlareZ123/bb6/actions/runs/46107124798). See the [full recurrence dossier](0RC-0LA-proof.md).

## Additional B1=0RC, C1=0RE child (28 November)

The independently reproducible first-hole partition for `C1=0RE` has **27,265 nodes**, 22,686 translated cycles, 214 sparse n-gram leaves and **four exceptional partial tables** of physical mass **700** (25+25+25+625). The four exact blank-root return costs are `40n+61`, `12n+41`, `16n+35`, and `8n+33`, with entry times 29, 49, 18, and 63 respectively. The four recurrence modules passed original-source Lean 4.36.0-rc2 and the axiom gate: M7 [46104882632](https://github.com/FlareZ123/bb6/actions/runs/46104882632), M4 [46105172131](https://github.com/FlareZ123/bb6/actions/runs/46105172131), M6 [46105351870](https://github.com/FlareZ123/bb6/actions/runs/46105351870), M5 [46105492096](https://github.com/FlareZ123/bb6/actions/runs/46105492096). The complete first-hole tree, all 214 n-gram certificates and four symbolic residuals were assembled into `Cover (WeightedBound 211) parent` in [CI 46107082911](https://github.com/FlareZ123/bb6/actions/runs/46107082911). See the [precise proof and partition dossier](0RC-0RE-proof.md). This is a source-accepted five-hole child, not the seven-hole Raw44 parent.


## Cross-agent B1=0RC, C1=1RA child

Agent8's [source emitter](../agent8-raw44/emit_c1ra_closed.cjs) composes the six hard one-hole residuals of the C1=1RA conditional tree. Three representatives have exact blank-root entries at step 53 and growth laws `20n+56`, `22n+58` and `24n+60`; the other three are literal E/F-renaming conjugates. The generated theorem `BB6.Agent8Raw44C1RAClosed.parent_cover : Cover (WeightedBound 211) parent` passed the original-source gate in [CI 46144122176](https://github.com/FlareZ123/bb6/actions/runs/46144122176). This closes the C1=1RA whole child; it does not close the seven-hole Raw44 parent.


## C1=0LE residual proofs accepted; full child Cover pending

The five-hole C1=0LE child has a reproducible 33,721-node partition with 45 hard residuals of total mass 19,125; the other 9,746,500 completions are already classified by halts, translated cycles, last-hole checks and n-gram certificates. Agent48 AutoPump found growth certificates for all 45 residuals, and every check_never theorem passed the original-source Lean kernel and axiom audit in [CI run 46166705089](https://github.com/FlareZ123/bb6/actions/runs/46166705089). The exact counts and reproducible candidate generator are in [0RC-0LE-frontier.md](0RC-0LE-frontier.md) and [prepare_0le_autopump.py](prepare_0le_autopump.py). CI run 46167386448 is assembling the finite Cover and E/F symmetry transfer; the full Cover (WeightedBound 373) is not yet claimed.
