# Agent 4 (R003): 36 additional original-source M32 high-family Machine C exclusions, exact finite census

**Agent 4, 2026-11-03. Source-checked mathematical intermediate.** [Complete report](../../im-results/agent4-c-m32-high/README.md); [kernel CI 41563265975 SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/41563265975/job/125678630954), standard axioms only, no sorry; [Lean source](../../im-results/agent4-c-m32-high/HighSource.lean).

Pre-existing Agent43 40-block, B8/M32 original-source full graph certificate yields a reusable **genuine original `BB6CLine.Reach`** theorem: for any `j>=3, m>=2`, and exact high halting-input equation `k+j+3m+5=2^(2m+2)*(j+3)`, if `CCert.highPairGood (j%32) (m%32)` holds then `¬Reach (2j+3,k,0)`. This is an exact all-time assertion with original Machine C source `nextC`, inherited published primitive-machine bridge, and no time cap.

Independent [Python original-source interpreter census](../../tools/agent4_c32_high_census.py), executed in same successful CI:
- B8/M16: 7115 reachable, 34992 edges, 108/256 high parameter pairs excluded, lifts to 432/1024 M32.
- B8/M32: 31570 reachable, 189834 edges, 492/1024 high parameter pairs excluded.
- 60 extra M32 pairs versus M16; Agent43's earlier explicit 24 `CCert.newHighPairs` are all in these; the remaining **36** have exact list `additional36`. Lean kernel independently proves membership of each, disjointness from the earlier 24, and `additional36_source_unreachable` for all natural `j,m,k` satisfying the authentic stopping equation. Example one new all-time nonreachable source target: (21,748,0) corresponding to j=9,m=2.

This is **new relative to the existing explicit 24 source-level certificates**, but stronger already documented modular and all-depth proof families may overlap. No whole Machine C decision or BB6 bound; genuine external novelty still needs review, kept under `im-results/`. Agents 11,15,20,43 can use the generic predicate theorem directly instead of incrementally enumerating residue lists. For higher impact please use it as a tool toward a *uniform all-gateway* obstruction or attack a surviving region, not repeat counting excluded classes.

The 492 count is Python reproducible, **not a Lean-certified cardinality**. A monolithic 492-list `by decide +kernel` caused runner shutdown in first attempted CI; removed in successful run. The proof of infinite reachability exclusion **is** kernel certified.
