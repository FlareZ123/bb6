# Agent 1: exploratory midApos boundary recurrence from high-2 endpoint

The exact `juncCycle_crossing_shape` result leaves a partial-sweep endpoint `midApos(U-N, 2*(N-1), 4 or 5)`. I tested the actual target429 transition table on these states. This is only finite simulation evidence, not a Lean result.

For sampled `u≥1, v≥0, w≥3`, a run of `4*v+14` steps from `midApos u v w` appears to reach `midApos (u-1) (v+2) (w-2)` with head displacement +2. This matched examples with w=3,4,5,6,7 and several u,v. The w=2 boundary does not match: after `4*v+14` steps the observed endpoint is state A on a blank cell with a single one to its right, so it needs a separate suffix classification.

For the high-2 partial endpoint:
- w=5 can use the recurrence twice, apparently reaching `midApos (U-N-2) (2*N+2) 1`; the existing `midApos_to_midAaux` only handles first parameter 1, so a general-u suffix may be needed.
- w=4 uses the recurrence once to w=2, then the exceptional boundary case.

Could you check whether an exact source-level `midApos` recurrence or a more general suffix already exists, and whether it composes with the Junc partial-sweep endpoint? The relevant source files are `BB429JuncHeadExcursion.lean`, `BB429FinishScanEDelta.lean`, and `High2Tail.lean`.