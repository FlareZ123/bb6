# Raw54 E1=0LE E0=1RF: checked leaf certificates and residual discovery

Scope: `1RB---_1RC---_0RD---_1LD0LE_1RF0LE_------`. **No aggregate child Cover or exact threshold is proved yet.** The frozen first-hole census gives 2,610 splits, 45,064 cycle leaves, 12,821 last leaves and 2,146 open leaves; total completion mass 9,765,625. Largest observed weighted halt 845 (844 live steps, one halt, zero incoming delay), table `1RB0RE_1RC0RC_0RD0RA_1LD0LE_1RF0LE_1RBHHH`.

Open-row SHA256 ae1d7c235351d32702026c6d6d416d01548c257aab30e98773ea88b81d63113c. Frozen bank (blob 56bf67275d597e354a0e827f6422ec68aa77f416) matches 1,967 rows; the 179 misses have SHA256 b5cc41348b6fb3a76c7abd71623b8b36f880a5c0579b7478df7c99b82d9e0461. All IDs below are zero-based among those misses.

## Checked original-source FAR certificates

The 39 DFAs in [rf-mutated.txt](rf-mutated.txt) were found by changing exactly one noninitial transition of a frozen bank DFA, keeping its orientation and state count. Every generated `BB6.Agent8Raw54.RF.M<i>.never` theorem was accepted individually by Lean 4.36.0-rc2, against the original FastFAR dependency closure rebuilt from source export artifact 15079633196. All 39 report only propext, Classical.choice and Quot.sound. They cover every compatible completion of the specified partial table. No native_decide or unproved lemma is used.

Regenerate the exact tables and FAR masks with [generate_rf_witnesses.py](generate_rf_witnesses.py) (uses existing original census, bank and mask generator). Compile each Raw54RFMut<ID>.lean separately to bound memory. All row identities are tied to the frozen census hashes above.

## Further candidate witnesses

The disjoint [rf-ngram.txt](rf-ngram.txt) records 67 more successful untrusted sparse n-gram searches (ID, width, abstract state count). The existing original sparse checker and emitter can regenerate these via `generate_rf_witnesses.py --sparse`. ID 93 has 1,005,602 abstract states at width 28, so a smaller witness is preferred before attempting a huge kernel reduction. See below for the affine and non-affine acceptance ledger. This does not establish completeness of the enumeration or a child upper bound.

The next mathematical work is to close the residuals and assemble a disjoint first-hole audit. Residual 54 has a complete paper argument below, awaiting original-source compilation.

## Checked affine and stack-return theorems

All 57 affine-growth theorems in [rf-growth.txt](rf-growth.txt) passed Lean 4.36.0-rc2 against the original SweepPumping source. The reproducible witness descriptions are (ID, blank entry time, state, left word, right word, repeat blocks, target left, target right, affine cost coefficient, intercept); letters A,B are the repetition placeholders. [generate_rf_growth.py](generate_rf_growth.py) replays the exact symbolic computations with the existing emitter, extending it to unequal-length block sweeps. Every step or arbitrary-tail block transfer is a kernel equality, and the final return has strictly positive cost. All 57 axiom reports are only propext and Quot.sound.

Eight non-affine counter cylinders are proved in [rf-hard.tar.xz](rf-hard.tar.xz) (Git blob 6aa5cdf8eca07ed2988c1b7967a411a7805b3477):

- Raw54RFStack011.lean: IDs 0,10,11. State A sections with left unary count 4n+3 and right stack alphabet 0000/0110, terminal 011. Reset on empty or zero block costs 4n+24 (0,10) or 4n+26 (11); pop costs 4 or 6. Entry 31. All compatible completions are nonhalting.
- Raw54RFStack579.lean: IDs 57,59,63. Analogous right alphabet of width 5 (57) or 4 (59,63), left count width*n+1. Reset costs width*n+12, pop costs respectively 7,10,4, entry 14.
- Raw54RF61.lean: right alphabet 0000/0110, A and C sections. A transfers to C on a marker; C accumulates an arbitrary unary count by popping markers and resets to A with 4n+12 steps on a zero or empty tail.
- Raw54RF62.lean: A right word is 0 followed by arbitrary pairs 00/11, C scans pairs. C increases counter by one per pair 11, and on 00 or empty returns in 2n+11 steps. A and C inductive closure covers arbitrary pairs and arbitrary counts.

All four module-level never theorems are kernel checked with propext and Quot.sound. The same archive includes Raw54RFBase.lean and Raw54RFAttained.lean, the latter proves the score 845 lower bound in the original weighted semantics, with standard propext, Classical.choice, Quot.sound axioms. Extract the archive into a directory on the Lean import path.

63 of the 67 sparse n-gram candidates have individually compiled with the original sparse kernel checker; the unaccepted IDs are 26,40,41,93. Eight non-affine discovery targets remain. The precise current residual set is **54,55,69,139,141,144,149,174,26,40,41,93** (12 total). No complete RF child Cover yet.

## Residual 54: complete paper-level binary-carry invariant (Lean candidate)

Table `1RB1LE_1RC1RA_0RD---_1LD0LE_1RF0LE_1LA0RF`, frozen miss 54. Write a zipper as (q,L,R), with L including the scanned cell and extending leftward; R extends rightward from the cell adjacent to the head. Both are zero-padded. Define G inductively by the empty word, each singleton b, and b0L for L in G and b in {0,1}. Let S(L,n) = (E,L,(11)^(n+1)011) for L in G, n >= 0. The authentic blank prefix reaches S([],0) after exactly 10 live moves.

The following two total returns use only defined transitions:

* If the scanned bit is 1, L is either [1] or 10T with T in G. The four moves E1,E0,F0,A1 give S(drop2(L),n+1). The spacer zero (explicit or implicit) guarantees E0. The right word acquires the pair 11, and the remaining left word is in G.
* If the scanned bit is 0 (also when L is empty), execute E0,F1, obtaining F with left word 101 tail(L), right word (11)^n 011. Each pair 11 in the right word can be crossed by two F1 moves, transferring 00 to the left beneath the scanned 1. After 2n moves the zipper is (F,1(00)^n 01 tail(L),011). Exactly ten moves F1,F0,A0,B1,A1,E1,E1,E0,F0,A1 now return to S((00)^n 1 tail(L),0). The ten-move equality follows directly by substituting n=0 or n=k+1; in both cases only the fixed leading cells are inspected. Replacing the first zero by one preserves G, as does adding pairs 00. Total return cost 2n+12.

Both successors stay in G with n >= 0 and have strictly positive cost. Inductively there are live prefixes of arbitrarily large length on the authentic blank orbit. No move reads C1, the only unspecified transition; therefore all 25 completions of that slot are nonhalting. This is a complete mathematical argument, not a finite trace extrapolation. The frozen census and bank digests were reproduced; 3,302 finite exact zipper regression checks of the return formulas also passed.

[Raw54RF54.lean](Raw54RF54.lean) states these equalities using the existing original-source SweepPumping and Raw54Return interfaces. **Candidate source only:** the current local Lean ZIP is missing 4,058,402 bytes (first part 300,138,496 bytes vs required 304,196,898; second part 304,196,898), and the container shell returned ClientError. No compiler acceptance is claimed. Before counting this as an accepted original-source leaf, compile the candidate and its dependency closure, check `never` axioms, and add it to the frozen audit ledger. This leaves 11 mathematical discovery targets, but still 12 without accepted certificates.
