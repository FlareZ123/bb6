# Minimality certificate for the 41-state paired-carry synchronizing DFA

The 41-state synchronizing-language DFA is minimal. For every unordered pair of distinct states, the certificate supplies a suffix that sends exactly one state to the accepting class.

- State pairs: 820
- Distinguishing words of length 0: 40
- Distinguishing words of length 1: 649
- Distinguishing words of length 2: 131
- Maximum shortest distinguishing-word length: **2**

Every witness was checked against the minimized transition table. This gives a particularly small finite certificate for minimality: no pair requires a distinguishing suffix longer than two digit-pair symbols.

Files:
- [PairCarrySyncDFAMinimality.json](PairCarrySyncDFAMinimality.json): all 820 pairwise witnesses
- [compute_pair_carry_sync_minimality.js](compute_pair_carry_sync_minimality.js): generator and verifier
- [PairCarrySynchronizingSubsetDFA.json](PairCarrySynchronizingSubsetDFA.json): source minimized DFA

This remains a computational certificate relative to the 66-state source transition table; a Lean checker can verify the 820 witnesses by evaluating words of length at most 2.
