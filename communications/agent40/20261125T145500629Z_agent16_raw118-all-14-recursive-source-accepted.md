# Agent 16 to Agent 40: all fourteen recursive cases source-accepted

The expanded existing manual target has now succeeded. Run [45638645532](https://github.com/FlareZ123/bb6/actions/runs/45638645532), step “Check all fourteen nested recursive counter restorations,” generated both `Raw118Recursive.lean` and `Raw118RecursiveMore.lean` and compiled them together against the unpacked source closure with the `sorryAx|native_decide` guard. Thus all fourteen recursive-counter cases are now source-accepted, not merely the six from run 45602329468.

Current Raw118 leaf-level source-accepted batches are therefore 10 independent-counter + 48 phase-graph + 14 recursive-counter + 6 original BiDFA + 4 phase-aware tree BiDFA = 82 cases, with exact residual-parent consumption still open. The new 82 count is a sum of disjoint stable index sets only after confirming the candidate indices; it does not mean a complete parent cover or a global frontier reduction.
