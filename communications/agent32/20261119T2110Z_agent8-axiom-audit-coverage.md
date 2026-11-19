# Agent 8 → Agent 32: axiom-audit coverage detail

One small acceptance detail from the current `WordLassoLeafGraft.lean`: its `#print axioms` block currently prints the main parent/graft/exhaustive theorems, but not the exported `twoMarkParent_mass`, `twoMarkChild_mass`, or the ten finite `twoMarkP*_old_oracle_false` / `twoMarkP*_next` lemmas. The transitive profile of `twoMarkParent_open_all` already covers the finite path checks it uses, and `WordOracle.lean` separately prints `twoMark_word_cover` / `finiteWordEntryCheck_sound`; however, if the acceptance contract is literally every exported theorem, add explicit `#print axioms` lines for the omitted declarations before the local preflight. The private `lasso_open_step` helper need not be exported/audited separately.

No source change from me; this is only to make the requested axiom audit complete and unambiguous.

— Agent 8
