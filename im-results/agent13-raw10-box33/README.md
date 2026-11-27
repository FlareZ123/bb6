# Raw10 rectangle 33, D0=2, B1=13: symbolic hard leaves

The two most resistant machines in this branch admit explicit nonhalting return maps.

- [8,20,11,13,1,13,2,23,4,0,2,21] (E1 halt): at a root A scanning 0 with blank left, the right stream is one free bit followed by base-four digits in {0,1,2}, least significant first. Root bit 0 becomes 1 in four moves. Root bit 1 initiates a scan over trailing digit-1 pairs; each is replaced by two ones. The first 0 or 2 leads to a clearing F sweep and returns to an allowed digit word. A finite word always has an implicit zero digit, so this is productive for every root. Box33BinaryCounter.lean proves this by list induction and strong induction on hypothetical halt time.
- [8,24,11,13,1,13,2,23,0,10,4,20] (E0 halt): after 33 moves, E scans a one with five ones to the left and zero to the right. Define R(m,r) as E with m ones on the left, scanned 1, r ones on the right; L(m,r) as R except for a single 0 between the scanned 1 and the right ones. The exact rules are R(m,r+5) → R(m+5,r) in 11 moves, R(m,0)=L(m,0), R(m,2) → L(m+2,1) in 14, L(m+2,r) → L(m+1,r+1) in 7, and L(1,r+2) → R(5,r) in 11. Consequently R(5,5k) → R(5,5k+2) → R(5,5(k+1)) forever. Box33UnarySweeper.lean proves all rules and the resulting nonhalting theorem.

Both files compiled in local Lean 4.36.0-rc2 using the exact C9Pair relative stream definitions (extracted from the existing conjugacy module); axioms propext and Quot.sound only. The canonical source projection and full branch coverage are separate next steps. No global bound is asserted.

## Exact source-cylinder closure (candidate)

The subrectangle fixes A0=8, B0=11, B1=13, C0=1, C1=13, D0=2 in the encoded convention, leaving A1, D1, E0, E1, F0, F1 unrestricted. Its mass is 25^6 = 244,140,625 tables. The six designated-final-halt slices contain 6·24^5 = 47,775,744 one-halt representatives, using the existing zero-delay-preserving reduction. The proposed weighted upper bound is 101; the other B1/D0 subrectangles of Raw10 rectangle 33 remain open.

`Box33BranchCore.lean` states the exact source restriction and all-six-slice soundness theorem. `Box33BranchTree.lean` checks complete branching and all witness types. `Box33BranchKnown.lean` attaches both return-map proofs and their E/F conjugates. `replay_branch.py` constructs the six untrusted proof trees with the existing deterministic trace, n-gram and lag/RLE infrastructure, reusing certified safe superboxes. It aborts on an unclosed leaf, and emits `Box33BranchClosure.sourceBound` only if every leaf has a candidate proof.

The independent 127-step first-hole run gave maximum observed primitive halting lengths (including the final halt) 87, 7, 90, 96, 90, 96 respectively; its open leaf counts were 282, 0, 152, 540, 152, 540. Those are finite observations, not an upper bound. Previous lag/RLE discovery and the symbolic hard leaves motivate the bound; until the complete generated closure passes, neither the 101 upper bound nor any canonical roster deletion is asserted.

## D0=14, D1=17 cylinder: eight exact non-halting return maps

The six free slots are A1, B1, E0, E1, F0, F1. This cylinder has 25^6 = 244,140,625 tables; all six one-halt slices have total 6·24^5 = 47,775,744 representatives. The 127-step first-hole scan produced 319,122,0,365,89,1298 open leaves for designated halt targets 1,3,8,9,10,11. Window saturation solved 267,111,0,319,63,1195 of them. Extended traces and lag/RLE saturation left eight singleton machines. The largest observed live halt length was 784, giving a candidate weighted bound of 790 (including at most five normalization-delay steps and the final halt).

The eight singletons are listed exactly in Box33D14Source.codes. All five independent Lean stream modules were checked locally (Lean 4.36.0-rc2, exact C9Pair stream definitions, only propext and Quot.sound). In particular:

* m0: the phase A with 6k+4 ones on the left and blank on the right returns to the corresponding phase k+1 after 16k+26 steps.
* m1: the left tape consists of 6k+3 ones followed by 0111, right blank; return cost 16k+43.
* m2/m3: 6k+2 ones on the left, right blank, return costs 16k+26 / 16k+24 respectively.
* m4/m5: left tape 1100(110)^(2k+1)11, right blank; return costs 26k+68 / 26k+70.
* b0/b1: at A the left tape has 3k+1 ones, and every third cell of the right stream (including scanned cell) is zero. The next-A rules preserve this guard, even for arbitrary infinite tails. The unique halt row A1 is never reached.

Box33D14Source connects these local step semantics to the actual encoded Frontier machine. Box33D14V17Known supplies the eight theorem-backed exact leaves to the existing replay generator. Run the shared workflow target weighted-tnf-raw10-box33-cylinder with raw_id 14,17,790. The canonical bridge and entire weighted bound remain pending source acceptance; no global residual count change or exact BB(6) claim is made.


## D0=17, E0=21: all nine previously open singleton machines

The direct all-completion tree for this six-fixed-row cylinder (25^6 = 244,140,625 completions) previously failed on nine exact tables after its long-trace and lag/RLE passes (run 45970269468). They are now addressed by explicit nonhalting certificates, rather than longer finite simulations. Eight are source accepted; the ninth has a finite invariant whose source bridge is under compilation. The full cylinder's proposed weighted bound 1,000,000 is not yet source accepted.

| Leaves | Exact proof | Source audit |
|---|---|---|
| m0, m1 | Unary phase 1^(5k), next phase k+1 in 36k+10 steps | 46021788697 passed |
| m6 | Unary phase 0·1^(5k+4), next phase k+1 in 12k+22 steps | 46021788697 passed |
| m3, m5, m7 | Translated cycles (entry, period, direction, boundary): (2130,89,L,-33), (2482,103,L,-17), (2092,1630,R,26) | 46021712667 passed |
| m2, m4 | Shared double-sweep family and finite macro initialization | 46023652110 passed |
| m8 | Closed regular tape-language invariant, 39-state partial DFA | finite certificate computed, full Lean bridge pending |

The exact machine codes and canonical projections are in Box33D17V21Source.lean and Box33D17V21Cycles.lean. The double-sweep proof, in Box33D17V21Double*.lean, has a general rule on left stream 1^11 0^3 1^(2n) 0^3 l with blank right: it returns to 1^11 0^3 1^(2n+8) l in 10n+123 (m2) or 10n+129 (m4) ordinary moves. For X(n,g,k)=1^11 0^3 1^(2n) 0^g 1^(2k), the rule consumes three gap zeros and adds four to n; the short-gap exit X(n+1,2,k+1) reaches P(2n,k+4)=1^17 0^(2n) 1^(2(k+4)). The P(g+6,k) phase reaches X(12,g,k). The finite proof from blank reduces through these phases to X(140,0,13), equal to the permanent family phase 153. No inference from observed growth is required.

### m8: finite-state return-map invariant synthesis

The last table is [8,6,11,2,1,13,17,19,21,3,4,0], equivalently 1RB0RB_1LC0RA_0LA0LD_0LE1LE_0LF1LA_1RA---. At state A with scanned cell and next cell both zero, write S(l,r)=A(l,00r) with both streams nearest-first. Group left cells into pair symbols 0=00, 1=01, 2=10, 3=11. A left-sweep configuration stores one buffered pair p and an unread pair stream. On reading a pair a, the exact macro either consumes one pair of input and prepends a right pair, or turns. The emitted symbol b is 0 for right pair 11 and 1 for right pair 01; all of these right pairs can be transferred back to the left by the exact two-step rule A(l,(!b)1r) -> A(0b l,r).

The return-map transducer reads the left pair stream from the head towards the tail. Its first input is stored in the buffer. The following table gives (new buffer, emitted left-pair word), or turn and copy. A dash is conservatively rejected.

| p | a=0 | a=1 | a=2 | a=3 |
|---|---|---|---|---|
| 0 | (2,1) | (3,1) | — | — |
| 1 | (1,0) | (0,0) | — | — |
| 2 | turn,112 | turn,113 | — | — |
| 3 | (2,0) | (3,0) | (0,0) | (1,0) |

The nonturn macros take 6, 14, 10 moves for p=0,1,3 respectively; the turn takes 6 moves, then right-sweep transfers the accumulated pairs in reverse stack order. The two turn-emitted 1 symbols are transferred before the retained 2 or 3 and unchanged input tail. The copy state simply copies every remaining pair. Every table entry is a finite identity on arbitrary tails, not a sample.

A deterministic construction searches for an inductive prefix safety language. Starting with the language of all infinite pair streams, iterate K_(n+1)=K_n intersect T^-1(K_n), rejecting a transition if the transducer rejects or if any emitted prefix leaves the monitor. Minimize each finite deterministic automaton. In each monitor, seed the edges on the all-zero path and repeatedly saturate edges visited by output streams of all paths using currently allowed input edges. Reject the abstract candidate if any output edge is forbidden by the monitor. At depth 30 this saturation stabilizes in seven rounds, with a 39-state DFA and 72 reachable input/transducer/output product states; 43 are active left-sweep triples and 28 are copy triples with identical input/output states. The initial triple accounts for the remaining state. The finite certificate itself is independent of the search algorithm: the all-zero path is accepted, every allowed input edge has a valid matching transducer action and allowed output path, and the copy states have equal monitor states.

The invariant on a concrete configuration uses the unread finite pair word (with implicit infinite zeros), input-monitor state i, buffer p, reversed list of emitted bits u, and output-monitor state o. The 43 stored triples (i,p,o) restrict the active left sweep. The accumulated output word is reverse(u), converted to pair symbols. Each nonturn macro consumes a pair, advances the product relation and pushes one bit onto u. Each turn preserves the language after the complete right sweep, so the next root admits the initial relation again. If a scan never turns, the positive-length nonturn macros themselves establish nonhalting. Thus there is no need to assert that every allowed word has a finite return time.

Reproduce the discovery with node discover_d17v21_m8.js. Box33D17V21Transducer.lean stores the DFA and relation, checks every finite obligation using kernel reduction, proves the primitive macro identities, and implements the positive-progress invariant argument. Box33D17V21Source.lean projects the authentic encoded source machine to the same local transition semantics. The final source acceptance must exclude sorryAx; the current compiler fallback is the existing targeted manual workflow because container.exec and python.exec both failed with ClientError before local Lean could run. No global BB(6) or canonical-roster decrement is claimed.
