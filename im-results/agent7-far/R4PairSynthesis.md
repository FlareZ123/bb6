# r4 pair-automaton certificate synthesis

Three new candidate nonhalting leaves for the authentic cut-six r4 parent `1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_------`. The exact finite FAR data are in [R4PairHits.lean](R4PairHits.lean). Independent Python and JavaScript saturation agreed, and Python checked every finite FAR validity condition. Original-source Lean acceptance is pending. These leaves are disjoint F0 ordinary children with F1 unassigned. The remaining 0LE and 1RC siblings are unresolved; 0RE is already source-proved by the pinned Cryptids graft. This work does not establish an exhaustive BB(6) bound.

The two-sided search uses DFAs L,R reading from the far blank end toward the head (head excluded), with both blank states fixed by zero. Let P(l,q,a,r) be the permitted abstract configuration. Require P(0,A,0,0), forbid P at every unassigned row, and enforce both direction closures. For a right move (w,R,q'), every L(l,w)=l' and R(r',b)=r imply P(l,q,a,r) -> P(l',q',b,r'); for a left move every L(l',b)=l and R(r,w)=r' imply the same conclusion. This is a finite inductive safety invariant, with all pop predecessors considered. The Boolean SAT encoding has no NFA mask composition. On each SAT hit retain the left DFA only and use conventional least FAR saturation; the existing checked FAR semantics is the proof consumer, not the SAT solver.

| F0 | DFA pair sizes | left DFA |
|---|---:|---|
| 0RA | 6 × 6 | 0, 1, 2, 1, 3, 4, 3, 5, 3, 2, 3, 5 |
| 1LE | 5 × 5 | 0, 1, 2, 4, 2, 3, 2, 4, 3, 3 |
| 1RE | 5 × 5 | 0, 1, 2, 3, 2, 1, 2, 4, 2, 4 |
