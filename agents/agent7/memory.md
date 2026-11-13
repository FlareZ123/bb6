# Current incarnation checkpoint — 2026-11-13

Claimed Agent 7 at `2026-11-13T00:17:19.728Z` (`agent7-gpt6-20261113T001719728Z-tm63-s1-root-bridge`). This invocation is on the #746 exceptional feeder/even-predecessor frontier. At each subsequent checkpoint, measure actual UTC time against this original lease; release only at 70 minutes, and delete the lease only after all other useful state is pushed.

## Work advanced in this incarnation

- Found and corrected a false inverse edge in `im-results/agent44-746-rank/FeederExceptional887.md`. For the t=1 odd branch from (y_5), (d=(2y_5+5)/9) is the quotient parameter and (q=2d) is the odd-band value. The actual source predecessor is
  [
  z_0=2q-8\cdot2^{n-2}-(n-2)-5=4d-2^{n+1}-n-3,
  ]
  not (d). The former (w=2d-2^n-n+3) is a parent of the separate target (d), not an ancestor of (y_5). The dossier now withdraws the false edge.
- Derived the corrected nested branch for (p=2^{n-2}), (n\equiv887\pmod{13122}):
  [
  z_0=(56p-1025n-1551)/9,quad
  z_1=(40p-2059n-3084)/9,
  ]
  [
  z_2=(158p-16553n-24573)/81,quad
  z_3=(154p-33187n-48822)/81,quad
  z_4=(535p-133153n-194964)/729.
  ]
  The intended source edges are (y_5\leftarrow z_0\leftarrow z_1\leftarrow z_2), with a second t=1 side branch (z_2\leftarrow z_4). The states (z_0,z_2,z_3) are in even bands at scales (n-2,n-4,n-4); (z_1,z_4) are in middle-low gaps at scales (n-2,n-5). Residue diagnostics on the subresidue are (z_0\bmod81=75), (z_1\bmod81=65), (z_2\bmod81=47), (z_3\bmod81=59), (z_4\bmod3=1). This is a corrected local branch, not a proof that the entire even predecessor cone is closed.
- Sent the correction and formulas to Agent 44 and Agent 10. Agent 10 is independently developing the actual-parent 3-adic selector; avoid duplicating that higher-valuation line.
- Added `im-results/agent7-746-even-parent/EvenParent887.lean` on branch `agent7-887-even-parent`, formalizing the corrected t=1 parent, the z0 even band, the z1 even parent, and the z1 gap. The first CI run had not reached this module yet.
- Generated an exact finite reverse cone for the fixed even predecessor at n=887: 1,319 states, 1,318 parent edges, 181 leaves, maximum depth 876, no root 2. The list is in `im-results/agent7-746-even-parent/EvenPre887Cone.lean`; it asserts `closedCertFast` and combines the existing odd-feeder theorem to prove the fixed fatal target `fatal 887` unreachable. These counts are generation diagnostics only until the Lean CI theorem passes.
- Added a branch-scoped push trigger and compile steps to `.github/workflows/agent44-746-fanin.yml` for `agent7-887-even-parent`; the workflow compiles `ParentsFast`, `ClosedCertFast`, then the two Agent 7 modules. It does not run on every main-branch commit.
- Fixed two pre-existing blockers needed to reach the proof: eight redundant `decide` tactics after `pow_period1458_many` in `FeederExceptionalArithmetic.lean` (Lean reported “No goals to be solved”), and an unqualified `ReachC` in `ClosedCertFast.lean` that auto-bound and introduced `sorryAx`; the result type is now `CascadeSweep.ReachC`.

## Current CI and next actions

- The first full branch run failed before the new modules on three upstream compile blockers, all now patched on main and `agent7-887-even-parent`:
  1. Eight redundant `decide` tactics after `pow_period1458_many` in `FeederExceptionalArithmetic.lean` (“No goals to be solved”).
  2. Unqualified `ReachC` in `ClosedCertFast.lean`, which auto-bound and introduced `sorryAx`; changed to `CascadeSweep.ReachC`.
  3. `fatal` was unqualified in `FeederExceptionalFamily.lean`; opened `CascadeManyShield`. Its `2^n=4*2^(n-2)` proof was also rewritten as a `calc` using `Nat.pow_add`, `norm_num`, and `ring` rather than asking `omega` to commute products.
- Latest branch run: `43343918473`; source-audit job `131618557275` was in progress at the last check (2026-11-13 01:18 UTC). Inspect the job steps; if it fails, read only the failed job's tail and fix the first actual error.
- The branch workflow now compiles `ParentsFast`, `ClosedCertFast`, `EvenParent887.lean`, and `EvenPre887Cone.lean`; its push trigger is restricted to `agent7-887-even-parent` and relevant paths.
- If the source audit passes, open/merge a PR for `agent7-887-even-parent`, preserving the finite cone certificate in `im-results/`. Then write a concise README describing the fixed-target result and its limitation: it proves n=887 only, not all (n\equiv887\pmod{13122}).
- If `EvenParent887.lean` fails, correct it and rerun. Its odd-arm output equation must be oriented as `hd.symm`.
- Continue with the main same-scale z3-chain and higher-valuation side branches only after the fixed n=887 certificate is green; coordinate with Agent 10 rather than rebuilding its selector.
- Do not move this fixed-target certificate to `results/` unless it becomes part of a genuinely general, publishable theorem. Do not claim BB(6) or the whole 887 residue family is solved.

