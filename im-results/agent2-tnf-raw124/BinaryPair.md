# Common binary-carry invariant for raw124 / F1=1LA

Two previously difficult partial tables (open-list indices 1254 and 2919, zero based) have an explicit infinite return invariant:

- p0 = `1RB1LA_1RC0RE_0RD---_1LD1RE_0RB1LF_0LF1LA`
- p1 = `1RB1RE_1RC0RE_0RD---_1LD1RE_0RB1LF_0LF1LA`

The C1 entry is never queried, so each argument applies to all 25 compatible completions. This is a paper-level nonhalting proof with finite framed rewrite rules checked locally; full original-source Lean composition is not yet accepted. It does not establish the entire 1LA branch or raw124 upper bound.

## Coordinate convention and invariant

E(L,R) and F(L,R) denote the respective state, left stack including scanned cell, and right stack, both nearest-first and zero padded. Concatenation is implicit. Let P=1101101001, z=0000. Encode a left Boolean digit as 00 or 01 and a right digit as 0000 or 0001. The invariant section is

H(t,w,r) = E(1 z^t 0^11 P enc2(w), enc4(r)).

The blank start reaches H(1,[],[]) after 441 ordinary transitions for p0, 485 for p1 (finite exact trace). Both finite digit lists are zero padded. Choose i and u with w=1^i 0 u, using the first implicit zero if necessary. Each epoch increments the left encoded binary counter, w'=0^i 1 u. The right update is:

- if t=s+1, next section H(0,w',0^s 1 r);
- if t=0 and r=1^j 0 v (using the first implicit zero if needed), next section H(j+1,w',v).

This is a total transition on finite words and natural t. Every epoch executes positive time without the unassigned C1 transition, proving nonhalting of every compatible completion.

## Exact framed primitive rewrite rules

In the table all L,R are arbitrary finite frames, and each arrow uses only assigned transitions without inspecting unspecified cells. Costs are p0/p1 where distinct. The rules are directly reproduced by openRun with both closed flags false (BlockPump.lean).

| Source | Destination | Ordinary moves |
|---|---|---:|
| E(1L,R) | F(L,1R) | 1 |
| F(0000L,R) | F(L,0000R) | 4 |
| F(0^11 P L,R) | E(10000011L,01 0^11 R) | 37/45 |
| E(100000110L,R) | E(101L,000001R) | 10/12 |
| E(10110L,R) | E(101L,01R) | 6/8 |
| E(1010L,R) | E(001L,1R) | 5 |
| E(0L,10R) | E(000L,R) | 2 |
| E(000L,0000101 0^11 R) | E(00101101001L,0010001000R) | 136/142 |
| E(0L,0010R) | E(01010L,R) | 4 |
| E(0L,000R) | E(101L,1R) | 10 |
| E(0L,11R) | E(100L,R) | 2 |

Here 0^11 means eleven zero symbols; powers of a parenthesized word repeat the entire word.

## Composition

First three rules, with the second repeated t times, take H(t,w,r) to E(10000011 enc2(w), 01 0^11 z^t 1 enc4(r)).

For arbitrary i and frames U,R, the next four rules yield the carry transformation
E(10000011 (01)^i 00 U,R) -> E(000 (00)^i 01 U,00001 R).
Use (01)^i 0=0(10)^i to expose the carry-init rule, then repeat the carry-sweep rule i times, use carry-exit, and repeat the 10-right transfer i+1 times; the required identity is 1(01)^i000001=(10)^(i+1)00001. Inserting the actual right frame and applying the middle rule produces
E(00101101001 enc2(w'), 0010001000 z^t 1 enc4(r)).

For every K>=0 and arbitrary W,V the final-phase transformation is
E(00101101001 W,(0010)^K 000 V) -> E(1 z^K 000 P W,V).
Apply the 0010-right sweep K times, the right-000 rule, the carry-sweep 2K times, carry-exit, the 10-right sweep 2K times, then right-11. The identities (1010)^K=(10)^(2K), 1(01)^(2K)1=(10)^(2K)11, and (00)^(2K)=z^K give the stated endpoint.

If t=s+1 the intermediate right word is (0010)^2 000 z^s 0001 enc4(r); select K=2, V=z^s 0001 enc4(r). If t=0 and r=1^j 0 v, it is (0010)^(j+3)000 enc4(v), using 001(0001)^j=(0010)^j001; select K=j+3. Since z^2 000=0^11, both outcomes are exactly the claimed invariant sections.

Trailing implicit zero digits can be explicitly appended to each encoded stack whenever the input word is all ones. Zero padding leaves the physical infinite tape unchanged. Every rule preserves arbitrary frames and uses only defined rows. Induction over epochs gives arbitrarily long live primitive prefixes starting at the actual blank root, rather than mere long bounded simulation.

## Acceptance boundary

Lean 4.36.0-rc2 locally accepted individual framed rule checks and the source-derived sweep infrastructure. The full symbolic composition and zero-padding-to-raw-run adapter are being formalized; no original-source CI success is claimed. The new proof is a candidate leaf-level contribution, not an accepted roster graft, and does not establish BB(6).
