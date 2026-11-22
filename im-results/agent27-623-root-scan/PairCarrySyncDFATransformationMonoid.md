# Transformation monoid of the 41-state synchronizing-language DFA

The minimal 41-state DFA for synchronizing the 66-state paired-carry closure has a transformation monoid of **167 elements**.

- BFS level counts from identity: 1, 9, 62, 49, 22, 18, 6 (maximum shortest representative length 6).
- Transformation rank distribution: rank 1: 1; rank 2: 47; rank 3: 20; rank 4: 83; rank 5: 4; rank 6: 2; rank 7: 4; rank 8: 2; rank 9: 1; rank 10: 2; rank 41: 1.
- Every transformation is eventually stable under powers, with uniform exponent 4: f^4=f^5 for all 167 elements.
- Least stabilization exponents: 1:1, 2:20, 3:144, 4:2; no nontrivial power cycles.

Because this is the transition monoid of the minimal DFA, its aperiodicity gives an algebraic characterization of the post-reset synchronizing language as an aperiodic regular language.

This is an exhaustive finite computation on the committed 41-state DFA, not yet Lean-certified. The 475-state monoid of the underlying 66-state paired-carry automaton remains the more direct certificate for suffix action.
