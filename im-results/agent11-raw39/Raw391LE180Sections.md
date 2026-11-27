# Raw39/1LE 180: exact A-return and rational sweep reduction

Status: intermediate mathematical reduction and finite automata experiment; **not a nonhalting proof**. Literal frozen leaf 180 is `1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---` (normalized open SHA256 4b8403493d8001bc6c1dacff454c53f2648e623315f435b4be761c5c5dca1451). F1 is the only undefined transition.

At an A visit write x#y, with x in physical left-to-right order and y starting at the scanned cell. Arbitrarily pad both ends with zeroes. If y starts with 0, the exhaustive prefix decision table below gives the next A visit: replace prefix u with v, move # past h bits of v, in t original transitions.

|u|v|h|t|
|---|---|---:|---:|
|0000|1011|2|6|
|0001|1100|4|4|
|00100|10111|2|10|
|00101|11000|5|7|
|00110|11011|3|11|
|00111|11100|5|9|
|01000|10111|2|8|
|01001|11000|5|5|
|01010|11011|3|9|
|01011|11100|5|7|

The sole other zero-start prefix is 011, which queries F1 after two live steps. These disjoint prefixes exhaust 0-start infinite binary words. The finite traces never read outside their consumed prefixes. If the scanned bit is 1, the left word has a unique suffix a01^j (with sufficient padding). A1 followed by E1^j and E0 returns A in j+2 steps, rewriting a01^j#1 to #a0^(j+1)1. This follows directly by induction on j; a finite-support tape always has a zero left of the head. Hence every maximal live section returns to A, and a first undefined query must arise at an A visit with right prefix 011.

## Sweep-level exact abstraction

The relation R consists of zero or more A0 returns, and L zero or more A1 returns. On finite padded words these are rational transductions:

* R copies x, consumes #, performs any sequence of full-push rows (h=|v|), then either emits # and copies the suffix or performs one bounce row (h<|v|), emitting # at its internal cut, and copies the suffix. A bounce leads to scanned 1, so no further A0 is possible.
* L includes identity. Otherwise copy left prefix, emit #, copy bit a, map 0 to 0, map zero or more 1 to 0; repeat zero or more blocks 10 1^j -> 10 0^j, consume old #, copy the required 1 and suffix. This is exactly repeated left returns: each intermediate a must be 1. Restrict to sufficient finite padding; every finite actual computation fits some such interval.

Thus any regular language K containing all padded blanks 0*#0*, disjoint from the bad language (0|1)*#011(0|1)*, and closed under R and L, proves nonhalting for every compatible completion. No bounded simulation premise is needed. Closure is decidable by finite product reachability; this is a sufficient certificate, not a claim that such a regular K exists.

## Finite inverse experiment

Starting with bad, take alternating exact inverse images under R then L, including identity in each. Determinize and minimize after each. State counts for 28 successive images:
9,22,40,71,101,152,212,314,437,636,843,1190,1591,2195,2858,3790,4863,6317,8048,10285,13002,16299,20484,25250,31498,38191,47436,56734.
All are disjoint from padded blanks. This is a finite sweep-alternation exclusion (each sweep can have arbitrary length), not an unbounded proof. Forward languages grow more slowly; guarded automaton folding has not yet yielded a closed invariant. The source script recreates exact inverse images and checks disjointness. Local Lean installed but exact repository checkout is unavailable due DNS; no source-level theorem for this leaf has yet been accepted.
