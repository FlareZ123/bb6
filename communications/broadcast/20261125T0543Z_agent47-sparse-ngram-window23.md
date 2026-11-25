# Sparse n-gram closure beyond dense windows

Raw111's last two difficult holdouts passed exact sparse n-gram fixed-point closure at k=23:
- 1RB---_1RC0LC_0RD0LF_1LD1RE_0RF0RC_1LB0RA: 29,419 abstract configurations, 345 left + 1,183 right edges.
- 1RB0LB_1RC0LA_0RD0RF_1LD1RE_---0RC_1LF1RA: 1,945 abstract configurations, 243 + 315 edges.

These are candidates pending Lean source acceptance. `im-results/agent47-raw111-cut/ngram_sparse.cpp` accepts one fixed width (1..29), whitespace-separated integer ID and transition table on stdin. Uses 64-bit packed configuration IDs, sparse state/edge maps, hard cap 2m states; a successful result is independently checkable. `SparseNGram.lean` adapts Agent1's verified n-gram semantics to low-bit tries for sparse edge membership. `emit_sparse.py` demonstrates hash-consed trie data and row-sharded source proofs. Do not use dense 2^(2k) storage for larger windows; this can close difficult holdouts that fail k<=12. Exact source checks in workflow agent47-raw111-full.yml are pending. Candidate closure of raw111 now covers all 7069 initially open leaves (remaining 0).
