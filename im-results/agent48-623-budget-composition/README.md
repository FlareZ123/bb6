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

## Exact blank-root mass gap

`RootExclusion.lean` records three exact high-level root checkpoints:

- step 39: `D(79788,133932)`, mass 213720;
- step 40: `D(54138,239399)`, mass 293537;
- step 41: `D(185262,162438)`, mass 347700.

It iterates the pinned source theorem `next_strict_mass` to prove that every surviving blank-root state is in exactly one of these classes:

`a+d <= 213720`, or `(a,d)=(54138,239399)`, or `a+d >= 347700`.

Thus every synthetic predecessor with mass strictly between 213720 and 347700 is excluded from the blank-root orbit, except that mass alone leaves the unique step-40 state; the exact coordinate clause handles that exception. The three representative predecessors q1=(260178,20001), q2=(256010,19681), and q3=(272586,20951) are all excluded. q3 deliberately has the same mass as step 40 but different coordinates.

These Lean proofs are source-level drafts pending focused Lean 4.36.0-rc2 compilation. The exact root checkpoints are proved by `decide`; monotonicity is proved by induction using `next_strict_mass`.

## Finite family search

`scan_terminal_budget_family.js` is a reproducible independent BigInt transcription of the pinned source recurrence. It searches odd d in `[19681,24819]` and odd offsets s in `[-455,445]`, with q.a=13d+s even, and filters by the n=10 root band, `logOuterBudget` at K=16, the odd-far-left parent conditions, the depth-14/K-16 terminal-ratio-four source hypotheses, and the c=5/e=306 bridge bound.

The exact search returns **10,763** three-step halting candidates across **2,550** distinct d values. Their predecessor masses range from **275,691** to **347,691**, all strictly between the step-39 and step-41 masses. Exactly one has mass 293,537: q3=(272586,20951), which is not the step-40 root state. Hence the root mass-gap theorem excludes every candidate in this finite search domain.

This is computational evidence from a source transcription, not a proof that the family is complete outside the stated finite search domain. The generic bridge/budget implication is false; the blank-root mass gap excludes this particular large finite family, but no all-time root-history exclusion has been established.
