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
