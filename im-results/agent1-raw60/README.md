# Raw60 candidate classification

Canonical raw residual 60 (index 36), E1=1RA, parent `1RB---_1RC---_0RD---_1LD1RE_---1RA_------`, six holes. First hole A1 after seven ordinary transitions. This is a new candidate search, not a certified closure.

Run the existing agent2-tnf-raw99/enumerate.cpp on the parent (cutoff 1000, side-cycle window 256). Its deterministic census gives 14,534 splits, 252,125 side-cycle leaves, 69,602 last-hole leaves, 12,556 open leaves. Masses: cycle 220,279,925; halt 18,679,552; total-defined 1,670,448; open 3,510,700; total 244,140,625 = 25^6. Open-list SHA256 f99d4f305af5f37284edca62fa8ceba353ea363d67fd839f7933a47b092ee25a. Maximum weighted score in this finite census is 929 (928 ordinary transitions, zero incoming delay), table `1RB1LF_1RC0LB_0RD0RF_1LD1RE_HHH1RA_1RC1LB`.

The pooled bank from agent11-raw107/bank.txt, agent3-tnf-raw120/bank.txt, agent8-tnf-six/raw115/bank.txt, agent8-tnf-six/raw119/bank.txt contains 431 distinct valid numeric DFA codes of at most ten states, with first DFA symbol zero. The existing agent11-raw107/bank.cpp saturation checker finds 11,664 candidates, leaving 892 open. Exact Lean FAR and tree acceptance are still required. Targeted symbolic induction and additional FAR searches are in progress.

No accepted parent deletion is claimed. Reproduction: compile enumerate.cpp with C++17/O3; run on the parent in a scratch directory; compile bank.cpp with C++20/O3; pipe zero-based open indices and underscore-free codes into bank with the pooled bank file. All ordinary first-hole branches must be retained in the eventual source certificate.
