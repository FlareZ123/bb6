# Raw54 E1=0LE E0=1RF: checked leaf certificates and residual discovery

Scope: `1RB---_1RC---_0RD---_1LD0LE_1RF0LE_------`. **No aggregate child Cover or exact threshold is proved yet.** The frozen first-hole census gives 2,610 splits, 45,064 cycle leaves, 12,821 last leaves and 2,146 open leaves; total completion mass 9,765,625. Largest observed weighted halt 845 (844 live steps, one halt, zero incoming delay), table `1RB0RE_1RC0RC_0RD0RA_1LD0LE_1RF0LE_1RBHHH`.

Open-row SHA256 ae1d7c235351d32702026c6d6d416d01548c257aab30e98773ea88b81d63113c. Frozen bank (blob 56bf67275d597e354a0e827f6422ec68aa77f416) matches 1,967 rows; the 179 misses have SHA256 b5cc41348b6fb3a76c7abd71623b8b36f880a5c0579b7478df7c99b82d9e0461. All IDs below are zero-based among those misses.

## Checked original-source FAR certificates

The 39 DFAs in [rf-mutated.txt](rf-mutated.txt) were found by changing exactly one noninitial transition of a frozen bank DFA, keeping its orientation and state count. Every generated `BB6.Agent8Raw54.RF.M<i>.never` theorem was accepted individually by Lean 4.36.0-rc2, against the original FastFAR dependency closure rebuilt from source export artifact 15079633196. All 39 report only propext, Classical.choice and Quot.sound. They cover every compatible completion of the specified partial table. No native_decide or unproved lemma is used.

Regenerate the exact tables and FAR masks with [generate_rf_witnesses.py](generate_rf_witnesses.py) (uses existing original census, bank and mask generator). Compile each Raw54RFMut<ID>.lean separately to bound memory. All row identities are tied to the frozen census hashes above.

## Further candidate witnesses

The disjoint [rf-ngram.txt](rf-ngram.txt) records 67 more successful untrusted sparse n-gram searches (ID, width, abstract state count). The existing original sparse checker and emitter can regenerate these via `generate_rf_witnesses.py --sparse`. Their proof acceptance is in progress; ID 93 has 1,005,602 abstract states at width 28, so a smaller witness is preferred before attempting a huge kernel reduction. With the 39 checked FAR leaves and 67 n-gram candidates the unresolved discovery count is 73. This does not establish completeness of the enumeration or a child upper bound.

The next mathematical work is to derive exact section-return proofs for the remaining 73 candidates and assemble a disjoint first-hole audit.
