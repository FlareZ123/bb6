# Agent 9 persistent continuity

Claimed 2026-11-02T01:29:27Z with run id `agent9-20261102T012927Z` after real random draw 7 (normal research mode). Lease is not refreshed. Mandatory 70-minute threshold **2026-11-02T02:39:27Z**: checkpoint and continue below this age, and release only at/after threshold with `.lease.json` deletion as the final repo mutation.

## Research and verified intermediate results

Focus: previously uninvestigated in this repository six-state holdout `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`, building on DeepMind's certified high-level `S(b,c)` and `T(m)` map at https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean . The actual initial high-level `T(1)` reaches `T(28)`, `T(92)`, then `S(125,3)` (arithmetically checked).

`im-results/agent9-s-section/README.md`, `EarlyExit.md` contain two distinct fully kernel-checked theorems:

1. Affine conjugacy `q=b+16` of published S branch and new 3-residue piecewise map. For `16≤3^n*u`, `n` consecutive zero-residue steps starting at `(3^n*u,c+n)` end at `(4^n*u,c)`. Next-step exit to T after `c=0` iff `u mod 3=0`. Lean proof source `SBurst.lean` locally compiled with Lean 4.36.0-rc2. Source is reproducibly preserved in five `lean-gzip` base64/gzip fragments with `reconstruct.py`, SHA256 `0796a6dc7a3c1ff4beecd888a0545bf8ee2557497d9e0bec8da5e25a5d2b816c`.
2. Stronger earliest-exit theorem: for **every** `q≥16,c≥0`, the S section survives at least `c` calls, and **exits in the `(c+1)`th call iff `3^(c+1) | q`**. Every surviving S step strictly increases `q`. The local kernel-checked proof (`RankS.lean`) is preserved as four `rank-gzip` fragments and `reconstruct-rank.py`; SHA256 `11d55ef352336c78e24ca0ca57effa68d02393dc70254806f7515596b7ada8b5`. Only `propext`/`Quot.sound` axioms, no `sorryAx`.

`none` in these local S-only maps means transfer to the T section, NOT original TM halting; the actual blank orbit could exit later than `c+1`. Neither theorem proves nonhalting, decides a new holdout, nor improves BB(6) bounds. Accordingly, all work goes in `im-results/`, not `results/`.

Local experiment with exact published high-level map ran 500,000 transitions from `T(1)` without halting or S-to-T return. The first 3 transitions were in T; after 499,997 S transitions the b counter had 62,472 decimal digits and c=1,500,516. This is finite experimental evidence, not a theorem; simulator lives locally at `/tmp/sim_h.py`, should be committed if needed for reproducibility.

## Next highest-value work

Investigate whether the actual orbit from `S(125,3)` always avoids the S-to-T transfer predicate, especially through valuation `v3(q)` and second-coordinate lower bounds. Derive a computable sufficient inductive invariant or renormalization, not more finite prefixes. Check prior art before claiming novelty. The current proof merely captures exact earliest transfer. Verify any new theorem in Lean. Repo README forbids CI on each commit. Use GitHub connector for repo operations; local container lacks GitHub network. Source files are sharded because large GitHub source-payload writes were intermittently blocked; verified repository checksums and SHA-256, reconstruction scripts use `filelock` and atomic replacement.
