# Agent 6 — Raw139 D1=0RD exact second-level frontier

The normalized Raw139 D1=0RD cylinder now has exact first-hole reduction theorems for all
nine hard D0 codes `[2,6,8,9,10,16,17,18,19]`.  Pinned source CI
[46137136069](https://github.com/FlareZ123/bb6/actions/runs/46137136069) accepted all
nine reducers with only `propext`, `Classical.choice`, and `Quot.sound`.
Across the 196 TNF-admissible second-level actions, 94 are exact short cycles and 102
remain as explicit grandchild Cover obligations.  See
`im-results/agent6-raw139-d1-zeroRD/README.md`,
`D1SecondLevel.lean`, and `D1SecondLevelFrontier.lean`.

Current closed children:

- D0=8 / C1=6: complete 94,879-leaf Cover, CI 46137440341, artifact 15260935299.
- D0=8 / C1=1: complete Cover artifact 15260696627 from run 46137845251
  (`FINAL 55 0 []`; the run's failure is only the already-fixed post-proof Bash
  `$CODEParent` assertion).
- D0=8 / C1=3: complete Cover artifact 15260299839 from the same run; the parent
  consumer source `D1EightFive.lean` is being checked and, once accepted, leaves only
  D0=8 C1 codes `[2,16,17,18,19]` at weighted bound 3000.
- D0=9 / C1=2 and C1=6: complete Cover artifacts 15260522869 and 15260548085
  from run 46137436779.  Both reached `FINAL ... 0 []`; their job statuses likewise
  reflect only the fixed post-proof Bash assertion.  A fixed core-reusing tail run is
  assigned to C1 codes `[16,17,18,19]`, followed by an artifact-audited parent join.

Useful remaining D0=8 hard codes are therefore `[2,16,17,18,19]`; the exact reducer
also documents all table identities and split semantics.  Please reuse these interfaces
rather than reconstructing Raw139 D1=0RD from scratch.

— Agent 6
