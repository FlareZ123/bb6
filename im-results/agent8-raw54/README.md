# Raw54 E1=0LE, E0=1LB: five-hole child reduction

Canonical raw54: `1RB---_1RC---_0RD---_1LD0LE_------_------`.
The current child is `1RB---_1RC---_0RD---_1LD0LE_1LB0LE_------`.
First-hole enumeration gives 1,515 split, 25,133 cycle, 8,567 last-hole and 1,146 open nodes (25^5 raw completions); observed maximum weighted halt 451. **The full child audit has not passed original-source Lean.** No global roster cut follows.

Of 1,146 open nodes, 1,065 have FAR candidates (1,058 frozen-bank hits, seven additional hits), 49 have affine sweep proofs, eight have arbitrary-tail strong-induction proofs, eleven have sparse n-gram certificates, and all thirteen formerly unresolved one-hole tables now have new exact recurrence proofs. [unresolved.txt](unresolved.txt) is empty; this is the generated candidate ledger, not yet an accepted coverage theorem. The 49 affine, eight strong-induction and eleven n-gram witnesses were previously compiled against original sources from raw117 artifact 14997867504, source revision 988705d0e0d7de1b736777b1b66b324115d75fdb. All thirteen new nonhalting statements compile locally using the relevant original source definitions and transport lemmas extracted from Frontier, RootShift, SparseZipper, SweepPumping and Raw54Return. The full repository import closure and child audit remain pending.

## Two-leaf counter invariant

[Raw54Pair.lean](Raw54Pair.lean) handles IDs 2 and 72 (zero-based in the 88 original bank misses), which differ only at C1:
- 2: `1RB0RF_1RC1RA_0RD0LB_1LD0LE_1LB0LE_1RA---`;
- 72: `1RB0RF_1RC1RA_0RD1RB_1LD0LE_1LB0LE_1RA---`.

Let k count scanned groups of four ones, and w be a finite Boolean list encoding four-cell blocks 0000 and 0011 (right tape padded by zeros). At A the left word, nearest-first excluding the scanned zero, is (1111)^k 1010111. The right word including the scanned zero encodes w. Both blank runs enter (0,[]) after 21 and 19 steps, respectively.

The exact total return system, with positive primitive costs, is:
- (k,1::w) -> (k+1,w), cost 6 for ID 2 and 4 for ID 72;
- (k,0::w) -> (0,0^k 1::w), cost 12+4k;
- (k,[]) -> (0,0^k 1), cost 12+4k.

Here 0^k denotes k zero block digits. The reset uses a six-step prefix, a left sweep E1 that converts each four-one block to four zeros, and a six-step suffix. The rules close over every finite list, including the implicit blank suffix. Iterating the total map gives unbounded live prefixes without F1 for every assignment of that sole hole. Lean 4.36.0-rc2 checked the recurrence and the original-semantics never theorem with only propext and Quot.sound, in a local build of the relevant source excerpts. The full original repository dependency closure still needs compilation.

## Left-tape counter invariant for IDs 62 and 63

[Raw54LeftPair.lean](Raw54LeftPair.lean) handles these two partial tables, differing only at F1:
- 62: `1RB---_1RC1LE_0RD0RF_1LD0LE_1LB0LE_1RA0RC`;
- 63: `1RB---_1RC1LE_0RD0RF_1LD0LE_1LB0LE_1RA0RF`.

Both enter A after 11 steps with left zipper 0101 (nearest first, including scanned cell), right zipper 11. A general return configuration has left zipper 01 followed by little-endian digits encoded as 00 or 01; right zipper 11. The next return increments the finite binary word (empty word increments to [1], 0::w to 1::w, 1::w to 0::inc(w)). The five-step entry into B prepares a leftward carry, each 1 digit costs two steps and moves a pair of ones onto the right tape, and the first 0 or blank takes one step into C. If k ones were carried, both variants return to A in 2k+2 steps by restoring k zero digits. The exact return cost is 8+4k. The transport uses C/F alternating steps for ID 62 and an F-only sweep after the first C step for ID 63. Structural induction on the unprocessed digit list establishes a total positive-cost increment; the source-excerpt Lean build checks `never` with axioms propext and Quot.sound. Every A1 completion is nonhalting.

## Further right-tape counter variants (IDs 73 and 87)

[Raw54RightPair.lean](Raw54RightPair.lean) handles the two additional tables:
- 73: `1RB---_1RC0RB_0RD1RF_1LD0LE_1LB0LE_0LB1RA`;
- 87: `1RB---_1RC0RC_0RD1RF_1LD0LE_1LB0LE_1RC1RA`.

They use the same total four-bit digit recurrence as IDs 2 and 72. Their left anchors are 111000001 and 111111010 respectively; the blank entries are 33 and 49 steps. Each one-digit advance costs 4. Reset costs are 26+4k and 64+4k, consisting of the same six-step prefix and E1 block sweep, followed by a 20- or 58-step fixed suffix preserving the right tape. Both arbitrary-word recurrence and original-semantics nonhalting theorem compile locally using the relevant source excerpts, with only propext and Quot.sound. Every A1 completion is nonhalting.

## Unary and double-sweep growth

[Raw54Growth49.lean](Raw54Growth49.lean): from A with left zipper 0 followed by n ones and empty right zipper, the machine adds ten ones in exactly 4n+34 primitive steps. Entry after 34 steps; n=10.

[Raw54Growth50Pair.lean](Raw54Growth50Pair.lean): IDs 50 and 51 share two sweeps. A has left zipper 000 followed by n+1 ones, right zipper 2n+2 ones. The first phase consumes the right tape and creates n paired zero digits on the left. The drain processes each pair, producing a new right pair, then returns to the same family at n+1. Entry 11, epoch 12n+23 / 10n+21.

[Raw54Growth52.lean](Raw54Growth52.lean): A has left zipper 100 followed by j copies of 000 and n+1 ones, right empty. A double sweep replaces these with j+1 zero triples and n+2 ones, preserving A and empty right. Entry 17 at (j,n)=(0,2).

[Raw54Growth71.lean](Raw54Growth71.lean): A has left zipper 111111 followed by n copies of 001110, right zipper 2n ones, n>=1. A complete epoch has exact length 60n+110 and replaces n by n+1. The proof gives two independent arbitrarily long drains, each consuming a right 1 in nine steps and adding a left 0, followed by raises consuming two left zeros in twelve steps and creating a right pair. Entry 123 at n=1.

## Arbitrary-word invariants

[Raw54Word66.lean](Raw54Word66.lean): an arbitrary finite Boolean word, each digit encoded twice, is scanned into a stack of 11b1 blocks. Processing a leading pair 1b pushes b; processing a zero or implicit blank starts the unwind. Unwinding writes paired digits 0,!b; popping the base block returns to the A family with a true prefix. Entry 37 with word [1,0,1]. Both scanning and unwind use well-founded word/stack length.

[Raw54Word41.lean](Raw54Word41.lean): a two-phase return from A with left zipper 01 and right marker 01 followed by k+1 copies of 0111, then payload 0100000 and paired binary digits. The first phase transforms the marker and payload into a second phase with k copies of 0111 and payload 0100110100011. The second phase increments the little-endian paired binary payload and increases the original block count by one. The entry is 101 steps, k=0, word [1]. Each macro preserves an arbitrary tail; the digit recurrence includes the implicit blank case.

All thirteen new `never` theorems were checked locally in Lean 4.36.0-rc2 using the relevant original repository source definitions and transport proof excerpts, with only propext and Quot.sound. All source files and the generator integration are committed.

## Reproduction

The columns of sweeps.txt are the zero-based ID in the original 88 bank misses, table, state, left/right zipper words (- empty, V denotes rep P n), P, jump j, entry t, and cost coefficients a,b. Each witness proves run0 table t blank = family 0 and run0 table (a*n+b) (family n) = family (n+j) for every n, then uses orbit k = family (j*k). Example ID 3: E, empty left, right (001)^n 0011, entry 7, epoch cost 20n+52, jump 2.

```sh
python im-results/agent13-coverage/unpack.py
python im-results/agent8-raw54/generate.py --sweeps-only
python im-results/agent8-raw54/generate.py
python tools/lean_compile_closure.py --workdir /tmp/a8-raw54-cut --jobs 4 im-results/agent8-raw54/Raw54Cut.lean
```

The manual Agent 13 coverage target `weighted-tnf-agent8-raw54` generates and checks `BB6.Agent8Raw54.cover`, and produces a source manifest on success. The full audit must be checked before using its residual roster. Raw54 has other children; closure of this child alone cannot close the raw54 parent. Raw55/56 are distinct canonical siblings; raw126–129 are excluded by state-introduction canonicality.
