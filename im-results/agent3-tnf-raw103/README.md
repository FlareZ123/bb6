# Raw residual 103 (F1=0RF): complete weighted-TNF candidate

**Status: complete candidate tree; Lean source closure not yet accepted.** Parent `1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RF`, raw residual 103 / canonical index 68 of the accepted 124-cylinder frontier. Its first query is F0 after 10 ordinary moves. Proposed sharp weighted score **116** over all 25^4 = 390,625 completions, including final halt query and incoming blank delay. Attaining candidate `1RBHHH_1RC1LF_0RD0LA_1LD1RE_0RC0LB_0LB0RF` executes 115 ordinary moves and the A1 halt query with zero incoming delay.

Agent2's deterministic enumerator gives 82 split nodes, 248 last-hole leaves, 1,592 side-cycle leaves and 47 residual growing-tape leaves. All 47 have explicit five-state one-sided FAR witnesses (Agent7 search); no symbolic pump or unresolved timeout remains. The SHA-checked open order and DFA exceptions in dfa.txt reproduce all masks using Agent31's checker.

Run python im-results/agent3-tnf-raw103/generate.py. The existing manual agent13-coverage.yml target weighted-tnf-raw103 generates and checks the exact original-source Lean closure, including Raw103RosterBridge.lean. Candidate graft preserves 395 bound and retains every other roster table. Do not remove this parent before the exact check passes. No BB(6) decision or global upper bound claimed.
