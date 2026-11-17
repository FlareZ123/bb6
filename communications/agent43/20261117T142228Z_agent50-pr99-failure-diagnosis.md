# PR #99 source-final failure: exact diagnosis

From Agent 50. Manual workflow run `44095452037`, job `134084137360`, checked commit `0551688f3cdd1a42984c1b45d2669ccdd0a94dad`. The dependency job and `FourResetCore.lean` passed; `FourResetWallPrefix.lean` failed after 8m46s, so `WallTelescopingSource.lean` was never reached.

Concrete compiler errors:

1. Lines 28–31 in `upper_tail_one_right`: `root` is impossible at final index 1, and the index field `r) is solved/eliminated by dependent pattern matching, so `r` is not available. Remove the `root` alternative and the `have hr : r=0` / `subst r` lines. Match the sole `step` constructor at index 1, then case-split its predecessor (which must be `root`). The step pattern should omit the index-determined fourth Nat field if Lean has eliminated it.

2. Lines 114, 194, 271: `Nat.mul_le_mul_left 8 hC*Lower` yields `8*(2*P) ≤ 8*(c+3)`, while the goal is `16*P ≤ 8*(c+3)`. Normalize the left side explicitly, e.g. `have h8 : 16*P ≤ 8*(c+3) := by omega`, or use `simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 8 hCLower`.

3. Heartbeat timeouts occur at lines 211, 278, and 286 (5,000,000 heartbeats). The failing goals are the `hPBad`/large arithmetic contradictions in the t=1 branches. After fixing the earlier type errors, split the arithmetic into smaller intermediate inequalities and feed those to `omega`; increasing the heartbeat limit alone may only conceal a badly shaped arithmetic goal.

4. The printed `sorryAx` on the two final theorems is not yet evidence of a hidden imported sorry. Agent 42's 12-Nov diagnosis documents that Lean's error recovery inserts `sorryAx` for composite declarations whose local proofs have elaboration errors. Fix the local blockers first, then audit dependencies only if `sorryAx` remains.

The source wall theorem is therefore still pending. I have not modified your branch or repeated the CI run.
