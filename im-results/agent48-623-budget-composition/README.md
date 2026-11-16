# #623 terminal-budget composition counterexample

**Status: intermediate diagnostic; Lean source draft pending focused compile.** This is not a blank-root reachability result, does not show that #623 halts, and does not decide any machine. Its purpose is to falsify a proposed generic implication in the terminal-to-budget cancellation route.

## Exact synthetic source trajectory

Using the pinned #623 accelerated transition definitions, the following states satisfy:

`D(260178,20001) -> D(240172,60031) -> D(180132,180131) -> none`.

All three first counters are even. The final `none` is not the trivial odd-first-counter branch: from `D(180132,180131)`, the odd-right branch invokes `drainB 3 180131 3`, whose `evalA` recursion returns `none`.

The first state satisfies the far-left odd `logOuterBudget` at exponent 16:
- `9*20001 + 39 + 16 = 180064 <= 260178`;
- `14*20001 + 59 = 280073 <= 3^16 = 43046721`.

Its smaller coordinate lies in the n=10 band:
- `3^9 - 3 = 19680 <= 20001`;
- `20001 + 3 < 3^10 = 59049`.

The middle state is an odd far-left terminal parent. The source theorem `oddFar_terminal_ratio4_source` applies with depth 14 and mass exponent 16:
- block count `60031+3 = 60034 < 3^14`;
- mass bound `2*(240172+2*60031+10+3*14)+5 = 720577 < 3^16`;
- terminal ratio-four gap `|240172-4*60031| = 48 <= 16+5*14+29 = 115`.

The preceding root-ray bridge from the first state to the middle state has c=5 and exact error
`(240172-4*60031)-5-(260178-13*20001) = -122`,
which lies within the cancellation adapter's e=306 bound.

Consequently, the existing far/far cancellation adapter can derive `logOuterBudget 260178 20001 16` for the predecessor, while the next two transitions still lead to a halting state.

## Logical consequence

The existing two-step safety theorem for a budgeted predecessor only establishes that its child has a successor. In this trajectory, that successor is the terminal state `D(180132,180131)`, so the theorem's conclusion is true and no contradiction follows.

More strongly, the exact trajectory refutes a generic three-step-survival theorem from this `logOuterBudget` plus the n=10 scale hypotheses. Therefore the current bridge cannot be closed by merely strengthening the existing budget predicate's generic safety depth. A successful argument needs a genuinely blank-root-history invariant, a root-reachability exclusion for the predecessor, or another source theorem not implied by the present budget.

## Formal draft

[`Counterexample.lean`](Counterexample.lean) states the exact source transition computations, the source terminal-ratio theorem application, the root-band and bridge arithmetic, and the adapter conclusion. It uses kernel `decide` proofs and prints axioms. It has not yet passed a focused Lean 4.36.0-rc2 compile; do not cite it as kernel-verified until that check succeeds.

## Blank-root exclusion of this particular synthetic predecessor

`RootExclusion.lean` adds a source-level proof draft that this q is not itself on the blank-root orbit. The exact high-level root states are:

- step 39: `D(79788,133932)`, mass 213720;
- step 40: `D(54138,239399)`, mass 293537.

The pinned `next_strict_mass` theorem makes mass strictly increasing between any two surviving root visits. Since q has mass 280179, it cannot occur before step 40 (its mass would be at most 213720) or at/after step 40 (its mass would be at least 293537). The Lean draft proves the two checkpoints by `decide`, proves monotonicity by induction over `run`, and derives non-reachability. This is still pending focused compile.

This exclusion reinforces the logical point: the synthetic counterexample does not threaten the actual blank-root orbit, but it proves that the cancellation/budget inequalities alone do not encode the missing root-history information.
The same file now proves the stronger interval statement `run n = some (.D a d) -> a+d <= 213720 ∨ 293537 <= a+d` for every n. Thus the entire open mass interval `(213720,293537)` is absent from the blank-root orbit, not only this one synthetic predecessor. This relies on exact step-39/40 checkpoints and the source `next_strict_mass` theorem.
