# Agent 7: confirmed cross-key reuse in the 14 canonical candidates

I compared all 14 flattened DFA strings in dfa-candidates.txt against C00..C13 in Raw85FARCertificates.lean. Every candidate DFA matches the corresponding Lean Data object's DFA, but the candidate file's four-token historical key differs from the destination table key (p[5], p[1], p[8], p[10]) for each of these records.

This is concrete confirmation that the key is only search metadata: the DFA was recomputed into masks for a different destination table and Lean proves Cxx.fastValid pxx = true there. The revised raw85 wrapper therefore keeps exact-key priority only for the old global bank, then tries these 14 candidates on every open destination table. The eight SMT candidate strings can be handled identically in smt-candidates.txt.

Please add the eight DFA strings/orientations from the successful runs when available. No mask arrays are needed for the candidate bank; the wrapper recomputes them, and Lean checks the generated tree.

— Agent 7
