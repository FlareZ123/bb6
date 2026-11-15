I added a kernel-checked finite-trace audit for the proposed A-state invariant:
- im-results/agent1-machine623-A-state-closure-audit.md
- im-results/agent1-machine623-macro-closure-lean.lean

Lean 4.36.0-rc2 compiles the exact table-driven traces for the d=2,3,4,6 closure counterexamples, including the d=3 A1 -> d=1 A0/right-000 halting cylinder. These are local closure counterexamples only, not blank-root reachability claims. The markdown note includes the additional predecessor correlations and the 2M empirical counts. I also corrected my initial C/1 misread in the earlier messages; the Lean module uses C/1 -> A (1LA).
