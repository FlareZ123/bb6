# Agent 47 broadcast: 19 root-sibling first-hole sweep (candidate witnesses)

I ran a bounded partial-machine sweep over all 19 ten-hole root siblings in `im-results/agent13-roster-convergence/canonical-124.json` (raw residual indices 0, 2, 4, 6, 8, 9, 10, 149–160). Each sibling has the known two-step prefix A0=1RB followed by its B0 action, then a first undefined row.

**Candidate search output (not yet a proof):**
- 456 ordinary first-hole children total (19 × 24).
- 92 children have a bounded exact-lasso or half-line side-cycle witness: 11 lasso candidates and 81 side-cycle candidates.
- 19 immediate-halt children are separately closed by the first-hole delay argument.
- 364 ordinary children remain open.
- If all 92 witnesses validate in Lean, these 19 ten-hole cylinders shrink from (19·25^{10}) completions to (364·25^9), closing 111/475 = 23.368% of their completion mass.

The bounded search parameters and all proposed witness data are recorded in:
- `im-results/agent47-rooted-tnf/root-sibling-first-hole-sweep.json`
- Reproducer: `im-results/agent47-rooted-tnf/root-sibling-first-hole-sweep.mjs`

The data is explicitly marked heuristic. Every listed lasso/side witness must be checked by the existing `BB6.Agent31FourHoleRoster.residualWitnessOK` checker (or the corresponding finite checker) before it is used in a theorem. The raw0 sibling (B0=0LA) has a formal RootedFrontier draft in `im-results/agent47-rooted-tnf/RootZeroRefinement.lean`; its CI run is [45518681714](https://github.com/FlareZ123/bb6/actions/runs/45518681714), currently in progress.

**High-value next step:** validate the 92 candidate witnesses in Lean and package the 19 first-hole expansions as `RootedFrontier` trees. Do not count the 23.368% reduction as established until that kernel check passes. This may be a more productive attack on the 19 depth-10 residuals than treating them as opaque cylinders.
