# Agent 15: source-accepted U5 w=7 subcylinder

A new exact-source infinite exclusion is accepted:
\[
u=239+640r,\qquad r\ge0.
\]
This is the first closed subcylinder of the previously open
\(u=79+80T\) branch, with \(T=2+8r\).

The q=1 parent
\[
Q=(1720951+4596480r,\;9445113+25226880r)
\]
is odd/odd, has right coordinate at least 64, and sum \(16\bmod32\).
The exact odd/odd sum-16 iff gives two parents:
\[
P_0=(5583030+14911680r,\;7514070+20069280r),\quad
P_2=(1395756+3727920r,\;9607704+25661160r).
\]
Three exact six-even-right inverses from \(P_0\), and one from \(P_2\),
terminate in odd-right states with sum \(1\bmod4\). Agent11's
original-source blank_no_odd_sum_one excludes both. The existing
odd-W q=0 parent-fan lift then excludes
\[
P(u)=(6924072+18493440r,\;6843559+18278400r).
\]

Lean source: im-results/agent15-c-halting/U5Q0W7U79Mod640.lean
Readable derivation: im-results/agent15-c-halting/U5Q0W7U79Mod640.md
Synthesis: im-results/agent15-c-halting/README.md and
U5Q0W7SourceParentAnalysis.md

Original-source Lean 4.36.0-rc2 CI passed in run #46:
https://github.com/FlareZ123/bb6/actions/runs/45903781364
Both new theorem axiom profiles are [propext, Classical.choice, Quot.sound];
the sorryAx/_native rejection guard passed.

The U5 w=7 synthesis now has 13 disjoint source-accepted cylinders.
The excluded-density lower bound among root-compatible \(u=19\bmod20\)
rises from \(249/512\) to \(265/512\). The new cylinder contributes
\(1/32\) of that full family (or \(1/8\) of the previously open
\(u=79+80T\) branch). The other seven \(T\bmod8\) classes remain open.
This does not decide Machine C or BB(6).

Useful next target: examine \(T=6\bmod8\) using the even/even
sum-zero parent fan, but preserve the exact direct/bounce parent
alternatives; do not infer a universal exclusion from one branch.
