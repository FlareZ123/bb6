# Raw10 I: a two-sorted regular payload language and a conjectural exact successor

**Research status (2026-11-28, Agent 13):** NEW *computationally discovered* global invariant candidate, **not** an accepted Turing-machine nonhalting proof. The language-preservation/transition claims below are exhaustively tested on finite words through 12 four-bit symbols (6,480 words) but not yet proved for all lengths or all outer phase parameters. The finite-state description is substantially stronger than a fixed-prefix experiment: it prescribes a complete two-sorted inductive grammar, a total recursive successor, and an explicit machine-semantic equation requiring formal proof. Do not classify the original machine as decided until that equation has been proved in the original source semantics.

## Exact source and boundary

The original six-state table is `[8,24,11,18,1,13,17,3,12,0,4,21]`, equivalently `1RB1RF_1LC0RE_0LA0LD_0LE1LA_1RC---_1RA0LF`, with only E1 halting. The existing `MacroI` standalone source proves a 490-step blank entry to `phase(3,1010111 0∞)`, where `phase(j,r)=A(blank-left,01010010(0010)^j r)`. A directly reproduced 1500-step blank trace reaches `phase(7,10101 00001 0∞)`; at step 926 the earlier boundary is only `phase(5,10101 01 0∞)`. All words below are tape bits in **nearest-first order**; all suffixes are eventually zero.

A *section return* `F_j(U)` means running the original primitive table from `phase(j,10101 U 0∞)` until it first reaches `phase(j+2,10101 V 0∞)` with blank left and no halt. The phase index increases by TWO for each such return; the candidate successor is the composition `F_{j+2}(F_j(U))`, increasing j by FOUR. It is a common error to normalize both simulated stages to the same j and claim this alone proves the authentic orbit.

## Small regular grammar

Use seven four-bit symbols:
`Z=0000`, `P=0010`, `Q=0100`, `R=0101`, `S=1000`, `T=1010`, `U=1100`.
Let the mutually recursive *finite word* types be

```text
N ::= S B | R B | T | Q Q
B ::= ε | P | Q | U | Z N | P N
L ::= Z S B | Z R B
```

Concatenation is lexical. For a finite word, its bits are padded by implicit zeros to a multiple of four, and its trailing explicit zero bits are immaterial. Every member of L begins with Z; the genuine entry payload `00001` is `Z S ε` (padded `00001000`).

These productions are equivalent to a 19-context (bigram over four-bit symbols) graph inferred from 599 observed even-section returns. Unlike a simple finite-prefix cylinder, they constrain arbitrary-length internal block structure.

## Successor and concrete semantic conjecture

Define total mutually recursive functions on the **syntax** of N and B as follows (upper-case symbols denote the four-bit chunks):

```text
nextN(S B)  = R B
nextN(R B)  = S nextB(B)
nextN(T)    = Q Q
nextN(Q Q)  = S U

nextB(ε)    = P
nextB(P)    = Z T
nextB(Q)    = Z S ε
nextB(U)    = Q
nextB(Z N)  = P N
nextB(P N)  = Z nextN(N)
```

Every right-hand side belongs to the same N/B syntactic class *by construction*, hence the induced update `H(Z N)=Z nextN(N)` preserves L unconditionally as a statement about the abstract grammar.

**The decisive unproved original-machine theorem** is: for every odd outer phase index j reached from the 490-step blank entry (or, more strongly, every natural j), and every `N` represented by the grammar, the physical machine has some strictly positive finite transition count taking
`phase(j,10101 Z N 0∞)` **without halting** to `phase(j+4,10101 Z nextN(N) 0∞)`.
The proof must establish the exact tape geometry, finite step count, and original-machine stream/source bridge. Then the 1500-step root entry and strong induction on prospective halt times would prove genuine nonhalting of machine I.

The zero-carry branch is already a formal consequence of the existing arbitrary-suffix `evenPacket`, `oddPacket`, and `carryPacket` identities: uniformly in j and *arbitrary* infinite remainder r,
```text
run (650+128*j) (phase j (1010100001000 ++ r))
  = some (phase (j+4) (1010100000101 ++ r)).
```
This is `H(Z S B)=Z R B` on any suffix B; the missing branch is the propagated carry `H(Z R B)=Z S nextB(B)`, plus terminal and nested N/B cases. A separate Lean source `Box33D17V12IRegularToggle.lean` is intended to prove the displayed four-packet composition (its formal CI status must be checked; this note is not proof acceptance).

## Finite evidence (independent primitive-table simulation)

A fixed `Z N` bit word is placed with zero beyond its last explicit bit. The direct raw-code simulator returns by checking machine state A, blank left stream, and the exact `01010010(0010)^{j+2}10101` right boundary; it rejects a halt or timeout. For each of the **6,480** distinct grammar words with at most **12 four-bit symbols**, the genuine two-stage computation `F_5(F_3(U))` (not two normalized `F_3` calls) returned and **exactly matched** `Z nextN(N)`. Maximum tested nonzero payload length was 48 bits. No counterexample was observed. This is evidence, not a length-unbounded universal theorem.

The beginning of the genuine alternating return sequence is:
`11 -> 01 -> 00001 -> 00101 -> 00000101 -> 00100101 -> 00001000001 -> 00101000001 -> ...`, where each arrow advances the outer phase j by two. Starting from `00001`, every **second** arrow follows the displayed abstract successor; the intermediate arrow is `F_j(ZN)=001N`.

A much broader digit-only grammar (allowing all observed 4-bit blocks without two-sorted ordering) fails under successor; its synthetic inputs can reach E1. The two-sorted regular grammar is a genuine restriction. Separately, a guessed binary-additive scalar weight model was falsified at the 13th grammar iterate, so the update is **not** a simple fixed linear combination of the ordinary binary digits of the iteration count.

## Reproduce and priorities

`node im-results/agent13-raw10-box33/regular_i_grammar.js 12` enumerates all 6,480 words and reruns the literal original transition codes with phase indices 3 then 5, comparing against the recursive successor. Larger bounds are optional tests, not a replacement for proof.

**Best next step:** prove the arbitrary-length *carry* branch via a finite family of machine-local scan/relay identities and induction on the N/B grammar, using the existing `MacroI.packetLift` bridge to factor out the unbounded `(0010)^j` outer blocks. Then attach the standalone stream model to the original `BB6Coverage` semantics as in `Box33SourceBridge.lean` and audit all axioms. This is a plausible path to an actual unresolved BB(6) machine decision, not a completed claim.
