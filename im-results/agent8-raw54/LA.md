# Raw54 E1=0LE E0=1LA: candidate census and certificates

Scope: `1RB---_1RC---_0RD---_1LD0LE_1LA0LE_------`. The attaining lower bound is original-source kernel checked; no parent Cover has yet been checked.

[Raw54LAAttained.lean](Raw54LAAttained.lean) proves `attained`: a compatible machine halts after 544 live steps with zero incoming delay, and `lower_bound`: every universal weighted bound for this child is at least 545. Both compile with Lean 4.36.0-rc2 against the original source closure rebuilt from artifact 15079633196, with only propext, Classical.choice and Quot.sound (commit 1e174ef1a5b78c754cb5021a81937e9eab9f0cbb). The [exhaustive sharded generator](generate_la.py) targets the matching upper bound; source generation and complete kernel acceptance remain pending.

The existing first-hole enumerator (agent47-raw112-cut/enumerate_fast.cpp) gives 1,816 splits, 27,205 cycle leaves, 13,222 last leaves and 1,342 open leaves, total completion mass 9,765,625. Largest observed weighted halt 545 (544 moves, one halt, zero delay), table `1RB1RF_1RC0RA_0RD0LD_1LD0LE_1LA0LE_HHH0RC`. Open table SHA256 c6ce7be3631b4544b5528fd717af5628a4b885745f16a8170970ffcc049efb4f. The frozen Raw54 bank (blob 56bf67275d597e354a0e827f6422ec68aa77f416) matches 1178 rows, leaving 164 misses (SHA256 0abdd7b494f234417e9079f683c2066174dcd3649a5e89070baff4686af3220b). IDs below are zero-based among misses in enumeration order.

74 additional FAR candidates appear in la-mutated.txt. Sparse n-gram candidates, width: IDs:
- 4: 16 68 75
- 6: 31 51 67 82 87 102 105 121 123 132 137
- 8: 36 54 78 80 81 133 134
- 12: 32 34 52 58 106 107 109 141 142 147 148
- 16: 59 110 111 129 131
- 20: 135

Ten additional exact symbolic return candidates, for the existing raw112_multisweep generator. Columns ID, state, left, right, P, jump, entry, a,b (cost a*n+b; V denotes repetition variable, - empty):
```
2 E - 0011V 010011 1 7 18 26
13 D 0000001 1111V 1 4 37 2 34
79 C 0111V 11 0111 2 13 32 70
89 D 0000V1001 - 0 4 15 2 30
90 D 0000V1001 - 0 6 15 4 38
92 D 0000V1001 - 0 4 15 2 28
103 B 001 1111V 1 8 25 4 66
143 D 01110111 1111V 1 8 69 4 138
157 C - 101011111V 1 6 32 4 82
163 C 0111V 11 0111 2 11 28 60
```
All ten sweep `never` theorems accepted by Lean 4.36.0-rc2 against the original source closure (propext, Quot.sound); regenerate using [generate_la_witnesses.py](generate_la_witnesses.py).

## Original-source nonhalting proofs for recursive and alternating families

- [Raw54LANested.lean](Raw54LANested.lean), IDs 60,62,63,64,65,66: A has blank left and right 1^(3n+1) followed by 011101 or (in the last two variants) 000101. A positive-time fill lemma with arbitrary left tail changes a scanned zero to one, preserving the right parameter n and allowing either suffix. Preparation transforms the right run into n left triples of zeros; strong induction uses fills at j<n, each followed by a three-move pop raising j to j+1. This proves a total recursive return for arbitrary n, and the blank-left version raises n by one. Entry 27 or 29, n=1.
- [Raw54LAAlternating.lean](Raw54LAAlternating.lean), IDs 48,55,56,69,70,122: D has empty right, left 0011(01)^(4n). Two rounds of E left-pair and B right-quad sweeps give n -> n+1 in 48n+30 steps. The left sweep uses induction including the final implicit blank (some variants materialize a zero there). Blank entry 3.
- [Raw54LANestedD.lean](Raw54LANestedD.lean), IDs 76,77,144,145,161,162: D left 00 1^(3n+1) 01b, right empty, n>=1. A stronger arbitrary-tail D-to-B return consumes a right sequence of triples of zeros terminated by 011. A nested call at each strictly smaller level is composed with a 3- or 5-move delimiter macro. The B return is 1^(3n+3) 01b' with the original right tail; at the blank boundary it adds the next triple to D. Entry n=2 at 51,55,63, depending on variant.
- [Raw54LANestedTwo.lean](Raw54LANestedTwo.lean), IDs 119 and 138: separate recursive D-to-A and D-to-C returns with arbitrary left/right tails, fixed suffixes 011101 and 000100, and triple or pair zero-block drains. At the blank boundary they increment the unary parameter. Entry n=1 at 33 or 22 steps.

All 20 new grouped `never` theorems (including the six+six+six+two variants) compile against original source dependencies, only propext, Quot.sound, and where needed Classical.choice. Original five project source blobs were recovered from artifact 15048626150 and rebuilt from source, and the two RA core modules used by recursive families were rebuilt from their original GitHub source. No new axiom, finite-time extrapolation, or native_decide is used.

## Paired odd-run stack (IDs 126 and 127)

[Raw54LAPair126.lean](Raw54LAPair126.lean) proves universal blank-tape nonhalting for both one-hole cylinders:

- 126: `1RB1RA_1RC0RF_0RD---_1LD0LE_1LA0LE_1RD0RB`
- 127: `1RB1RA_1RC0RF_0RD---_1LD0LE_1LA0LE_1RD0RF`

Both share a section system at A scanning zero, with a left stack of odd zero/one-run frames and a right word of positive even one-runs separated by positive multiples of four zeros. Let a denote the number of leading left one-pairs. A P-section has an odd right one-run (at least three); a Q-section has three leading right zeros. With nonempty stack, a is even at P and odd at Q. Every nonbottom frame stores an even one-pair count. The exact P push costs 2n+16 moves for a first right run of length 2n+3; it installs a frame with zero-run 2n+1 and one-run 2a+1 and returns to Q with a=1. The Q drain of a nonminimal frame (or empty stack) costs 8+2a+8(a+1) and returns to P with a+1. A minimal-frame Q pop costs 10+2a and restores the next frame's counter b+1; its right gap has the required multiple-of-four structure because a is odd. Blank padding is handled by a proved bisimulation of the original zipper, not by a finite tape cutoff. The authentic blank is equivalent to the empty Q-section with a=0. Positive-time closure gives unbounded live prefixes, and the original run bridge yields `NeverHalts` for all compatible completions.

Lean 4.36.0-rc2 checked `BB6.Agent8Raw54.LA.Pair126.sectionReturn` and `BB6.Agent8Raw54.LA.Pair126.never` using rebuilt original source dependencies Frontier, Symmetry, RootShift, SparseZipper, SweepPumping from artifact 15048626150. Both report only propext and Quot.sound. Exact source commit 174a7238fb014cf9876ae35982c5c28e83101975; verified blob fd840ea652b3823929158d3dcc1cc84f9bf3cb95.

## Triple-cell counter and two-sided run stack (IDs 61 and 104)

- [Raw54LA61.lean](Raw54LA61.lean), ID 61: `1RB1LF_1RC0RB_0RD0RC_1LD0LE_1LA0LE_1LE---`. A four-section invariant uses arbitrary left Boolean digits encoded as triples 00b, a terminal 01, and right unary runs. The B/C/D/E scan converts a first run of length m+1 and second of length n into a left zero-run of length m and the new right suffix of length n+2 in m+2n+8 steps. Three-move A1 pops either transfer a digit into the right run or initiate a carry. The four-move terminal pop and 3k+9-step overflow rebuild the counter with one additional high digit. Exact blank entry is at 27 steps. Padded bisimulation handles missing terminal zeros. Both sectionReturn and never passed the original-source kernel with only propext and Quot.sound. Commit b19cc68354619e4bc2eca0af748d289008353baf, blob 9db17457ee0f2f4b23ac3a94c64892f49c1ca10b.
- [Raw54LA104.lean](Raw54LA104.lean), ID 104: `1RB---_1RC0RF_0RD0RC_1LD0LE_1LA0LE_1LF0LA`. At A scanning zero, the P and Q phases differ by a five-move transfer. Left frames have positive even one-runs, with zero gaps multiples of three and a top phase offset (2 at P, 1 at Q). Right internal one-runs have residue 2 mod 3 at the Q head and 1 mod 3 subsequently; zero gaps are positive odd; the terminal one-run has unrestricted length. For a first Q run of length a followed by a single zero, the a+5-step push consumes the next one and installs a left frame. For a gap of at least three, or the blank boundary, the 2a+s+8-step drain removes a left one-run of length s (possibly zero), decreases the left zero counter or pops a frame, and creates an odd gap s+1 plus a right run of length a+2. The abstract grammar is closed in both cases, including terminal padding. Exact blank entry 8 steps. sectionReturn and never passed Lean 4.36.0-rc2 on the same rebuilt source closure as Pair126, with only propext and Quot.sound. Commit 946be55286c6c4f5a1f3cc94c2a191c1b6320efe, blob 73f54e8eb2a2279f99a3432d252033f96a24569c.

The subsequent witness archives `la-proofs.tar.xz` and `la-hard.tar.xz` reduced the discovery backlog to IDs 37, 61, 104, 126, 127 before the paired theorem. The remaining known discovery target count is now **zero**, following the proof below. This is a discovery-ledger conclusion until the complete child Cover passes Lean. Earlier candidate lists above are discovery records; they are not a checked disjoint coverage partition. The attained score 545 is now checked; its optimality requires a complete checked child coverage audit, including ingestion of archived and newly proved witnesses.

The separate E0=1RF child has 2610 splits, 45064 cycles, 12821 last, 2146 open, observed maximum weighted score 845. Frozen bank hits 1967, misses 179. Open SHA ae1d7c235351d32702026c6d6d416d01548c257aab30e98773ea88b81d63113c; misses SHA b5cc41348b6fb3a76c7abd71623b8b36f880a5c0579b7478df7c99b82d9e0461. No further search on RF yet.

### LA ID 37: modulo-four run grammar

[Raw54LA37.lean](Raw54LA37.lean) proves the universal blank-start nonhalting theorem for `1RB0LF_1RC0RB_0RD0RC_1LD0LE_1LA0LE_0LB---`. The left stack consists of frames of the form `0^(4k+2)101`; the right word uses internal one-runs with lengths governed by the preceding one- or two-zero gap, plus an unrestricted terminal run. The A0 phase either pushes a frame or merges the first run, and the A1 phase pops a minimal frame or decreases the top frame counter. The exact primitive macro costs are a+6 and 2a+8 for the A0 branches, nine for a pop, and eight for the decrease or empty-stack branch. The auxiliary Q phase permits a sequence of pending pop prefixes. The blank entry takes 43 moves. All branches are positive and preserve the inductive grammar, including arbitrary terminal length and implicit zero padding. Lean 4.36.0-rc2 checked `sectionReturn` and `never` against the rebuilt original-source closure; axioms are propext and Quot.sound only. Commit 297fb15abe1d39bd2f04df6f4a8a49d2e0d04ffe, blob da7317ace353667f0ab7fb6477e543dfc708f9a9.
