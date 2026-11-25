# Raw112 candidate discovery

Physical partial table: `1RB---_1RC---_0RD---_1LD1RE_---1LC_------`. Six holes, 25^6 = 244140625 raw completions. Candidate discovery only, not a kernel-accepted closure.

The optimized enumerator shares known prefixes across sibling branches, and compares exact 64-bit tape windows (quick head-relative signatures can only reject cycle candidates). It uses the same first-hole branch ordering and side-cycle window as the earlier enumerator. Raw115 produced byte-identical tree and open files with both enumerators. Raw112 finished in ~8 seconds locally.

```
g++ -std=c++17 -O3 enumerate_fast.cpp -o enumerate_fast
./enumerate_fast 1RB---_1RC---_0RD---_1LD1RE_---1LC_------
```

25004 split, 446232 cycle, 115572 last-hole, 13289 open leaves. Cycle mass 216900600; halt mass 23115872; last-hole ordinary mass 2773728; open mass 1350425. Total 244140625. open.txt SHA256 61773d08354491c09508929b83a5090b564b7808e7dabf6b045d353c9ea2bf01; tree.json SHA256 93fc68780b240a41f294f311369b905a7b562f47378f9ad26e1d43e4a55c50df.

Use previous raw115 FAR and sweep generators with this open file and far-bank.txt. 12723 FAR hits; remaining 566 (mass 33950, unresolved.txt SHA256 4f8da69ac2fa75f2a59eb2dd0917e35803a7f8937f18945203f5240133ea720a); 435 single sweeps, 131 hard leaves (mass 4475, hard.txt SHA256 23805b6953da558d904471078a742f87767945ec835afd5ebe602fbb68d32f69). ngram.txt columns index-in-hard-file, width, abstract state count, left edge count, right edge count; 84 candidate certificates. late.txt identifies six actual first-hole queries (index, time, slot = 2*state+symbol), including t=91502, hence a local bound 7014 is false and the audit must use a larger bound (proposed 100000). 41 residual leaves remain. A timeout is never evidence of nonhalting. Source certificate construction is outstanding.

## Inductive return progress

Five explicit recursive carry proofs (IDs 27,101,102,107,108) are committed. ID27 exhausts lower pairs twice across a carry; the four related proofs exhaust pair words with exit state cycling A,C,B. A complete outer return adds six ones after two D-to-D returns.

IDs32–35 share a polynomial counter: A(a,b,X) has state A, left word 00X and right (10)^a 0 (10)^b 11. A(a,b+1,X) -> A(a+1,b,X) costs 6+4a. Drain b by induction, remove delimiter, and final sweep gives D with left 001111(11)^(a+b+1)0X. IDs32/33 increase both paired runs in the outer D state; IDs34/35 increase the unary run by six. ID51 is a two-block affine return in B, left 0(00)^n 1 0^n, empty right, cost 11+10n, blank entry t=1. make_poly.py emits these five proof candidates. All ten pass local Lean on exact copied semantic definitions and assumed sweep/return interfaces; original-source acceptance is pending. 31 of 41 residuals remain.

## Additional holdout closure candidates

Extra FAR search through size six and seeded randomized DFA mutation (sizes seven through twelve) finds 19 additional certificates listed by hard-file index in `far-extra.txt`. This includes ID77, independently proved by a nested symbolic counter. Codes consist of a reflection flag followed by two destinations per state in hexadecimal; direct certificate reconstruction checks every result.

For ID77, F(a,b) has left word 0(11)^(a+1)01·1^b and right 1^b. Transfer F(a+1,b) -> F(a,b+1) costs 9+4a, and reset F(0,n) -> F(n+1,0) costs 17+3n. Blank entry F(0,0) at t=10. Drain a by induction, then reset. `make_77.py` reconstructs the proof.

For ID62, E with empty left and right (01)^(2+12n) returns to the next parameter in 228+288n steps. ID73 uses (01)^(2+8n), cost 130+128n. Both enter at t=11. ID72 starts at t=58 in D with left 00(110)^(n+1)1^(4n+6), right empty; cost 103+48n to increment n. ID121 enters at t=129 in B with empty left and right 0^(n+4)1010^(n+2)10; return cost 62+6n. `make_affine.py` reproduces the four proofs. All symbolic proof bodies check against the local copied-semantic fixture; original-source acceptance remains pending.

**Two remaining candidate leaves: 10 and 15.** ID105 has a further FAR certificate; IDs6,100,103,106 have arbitrary-word or recursive exhaustion proofs, ID23 has a three-phase affine recurrence. Local fixture checks passed; original-source acceptance pending.

The archive `inductive-generators.tar.xz` contains the additional four generators and exact hard-table manifest. Run `python generate.py` to reconstruct the partial audit and its two explicit residual leaves. The source-audit workflow accepts mode raw112. The bound is 100000; no complete cylinder closure is asserted.
