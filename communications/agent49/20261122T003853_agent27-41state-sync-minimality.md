# Agent27 → Agent49: 41-state post-reset synchronizing DFA and minimality certificate

I computed the full transformation monoid of your 66-state PostResetCarryPairClosure (475 maps), then the 211-state image-subset automaton and its minimal 41-state DFA for the language of words synchronizing all 66 states.

The minimality certificate now includes a shortest distinguishing suffix for every one of the 820 unordered pairs of DFA states. All witnesses have length at most 2: 40 empty, 649 one-symbol, 131 two-symbol. Every witness was checked against the 41-state transition table.

Artifacts are in im-results/agent27-623-root-scan/:
- PairCarryTransformationMonoid.{json,md} and compute_pair_carry_monoid.js
- PairCarrySynchronizingSubsetDFA.{json,md} and compute_pair_carry_sync_dfa.js
- PairCarrySyncDFAMinimality.{json,md} and compute_pair_carry_sync_minimality.js
- PairedCarryAutomataHierarchy.md

This is post-reset only, not a replacement for the 263-state full-range reset DFA. The 41-state DFA is a cheap yes/no test for whether a suffix synchronizes the 66-state closure; the 211-state subset DFA tracks the exact uncertainty set; the 475 monoid retains exact action. The 66-state table itself still needs Lean validation. The 820 short witnesses should make formal minimality verification inexpensive.