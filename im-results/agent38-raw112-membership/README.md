# Raw112 membership and Raw121 roster extensions (intermediate)

This directory contains two separate finite-roster integrations. Neither is a complete BB(6) upper bound: every retained quotient Cover and a champion attainment witness remain explicit premises.

## Route A: Raw112 membership in Agent8's canonical70 roster

`Canonical69Raw112Membership.lean` imports `Canonical70Raw121Raw110RosterOnly`, `Raw112Base`, and `CanonicalRosterRefinement`. It does not import `Raw112ClosedCover`. By decidable table equality it checks that the Raw112 parent remains represented in the 70-entry roster and that grafting it gives 69 entries.

The existing `canonical70` job in `.github/workflows/agent47-raw114-graft.yml` now compiles this module as a second root, audits `parent_present` and `count`, and records the 69 count with an explicit statement that the Raw112 parent Cover is not assumed. Workflow change: commit `0c1e32cc09d675303dd4479dee4df894b8e8c37e`.

This proves only the finite membership/count fact. A 69-entry sound roster requires the source-accepted Raw112 parent Cover and a separate `graftRoster_sound` theorem.

## Route B: Raw121 cut from Agent31's canonical73 roster

`Canonical72Raw121Graft.lean` imports `Canonical73Raw110Composition` and the source-audited `Raw121Data`. It checks by `decide` that p121 survives the 73-entry raw107/raw114/raw117/raw112/raw110 roster, grafts it, and asserts a 72-entry count. Its sound theorem lifts Raw121's `WeightedBound 4063` to the common `6766859` bound and composes with the canonical73 dichotomy.

The existing `canonical73` job in `.github/workflows/agent47-raw114-graft.yml` now reconstructs Raw121 sources and compiles both the 73- and 72-root modules in one closure against the same Raw107 shared-core manifest. It audits `Raw121.all121` and the new 72-extension profiles, then uploads a second artifact named `canonical72-raw121-raw110-raw112-roster-only-certified`. Workflow change: commit `62e1c5208500ee3f8750f1356055c507aa725211`.

This is still a draft until the canonical73 source audit succeeds and the p121 membership/count computations compile. Even then it is a conditional 72-residual theorem, not BB(6) exactness.

## Current dependencies and next steps

- Raw121's parent theorem `BB6.Agent11Raw121.all121` at bound 4063 was source-accepted in CI run `45616647230`; the canonical73 job recompiles its source closure against the shared core.
- The Raw112 full parent Cover remains unaccepted. The failed run `45646559852` ended in GitHub runner shutdowns (exit 143) on four shards, with no Lean theorem diagnostic. Agent47 has been notified.
- The canonical72 shared-core run `45647053824` was still in progress at the latest checkpoint. If it uploads `raw107-canonical-shared-core`, dispatch the updated workflow with `target=canonical73` and `canonical76_run_id=45647053824`.
- If the 72 extension's membership or count check fails, record that result and do not claim the cut survives. If the canonical73/72 source audit succeeds, preserve the conditional status: all 72 residual Covers and the champion witness are still outstanding.
