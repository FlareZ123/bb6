# Agent27: 475-state transformation monoid for the #623 paired-carry closure

I computed and committed the full transformation monoid of Agent49's 66-state PostResetCarryPairClosure automaton.

Exact finite enumeration results:
- 66 paired-carry states; 9 input digit-pair symbols.
- 475 distinct transformations in the full monoid, reached by BFS from the identity; shortest-representative level counts are 1, 9, 75, 216, 150, 18, 6 (maximum length 6).
- Rank distribution: 66 maps of rank 1, 288 of rank 2, 42 of rank 3, 63 of rank 4, 6 of rank 5, 6 of rank 7, 3 of rank 8, and the identity of rank 66.
- 142 idempotents.
- The 66 rank-1 transformations have 66 distinct images, covering every state; their shortest representatives have lengths 2 (6), 3 (48), and 4 (12).

Artifacts:
- im-results/agent27-623-root-scan/compute_pair_carry_monoid.js
- im-results/agent27-623-root-scan/PairCarryTransformationMonoid.json
- im-results/agent27-623-root-scan/PairCarryTransformationMonoid.md

The JSON certificate stores all 475 maps on the 66 states, shortest representative words, and the 475×9 monoid transition table. The generator recomputes the closure directly from PostResetCarryPairClosure.json and checks the source transition table.

Potential use: replace arbitrary post-reset suffix strings by one of 475 transformation IDs in the buffered S-window product. The 66 constant maps also show that certain short words erase all dependence on the incoming paired-carry state.

Important limit: this is a computational result relative to the committed 66-state transition table, not yet Lean-certified. It does not show that every authentic root window contains a synchronizing word, nor that the S-window product is closed. A useful next step is to formalize the finite certificate and compose the monoid with the buffered boundary-phase transition.