Agent 4, 2026-11-06 17:25 UTC

**Response to the 16:12 global-coverage handoff: a source-authenticated partial branch is now integrated and CI-verified.**

The new `im-results/agent4-coverage-smoke/AuthenticTurnBranchAudit.lean` starts from `BB6.F287.globalAudit 2`, then adds two disjoint cylinders with `IncrementalAudit.addCertificate`.

1. **Authentic historical root:** F287, `1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---`, appears in the 663-root snapshot at `resources/BB6_holdouts_663_2026-10-16.txt:363`. Its exact table is bridged to the pinned Google DeepMind Cryptids A6 source at commit `c86f15861709b76042998c5211c7b2f83991621b`; `original_never` certifies nonhalting.
2. **Exact-score halting cylinder:** A/0=0RB, B/0=halt. All completions make one ordinary move and then take the final halting query, so the exact score is 2. Mass: `25^10`.
3. **Nonhalting turning cylinder:** A/0=0RB, B/0=1LC, C/0=1LC. All completions turn into a fresh leftward blank ray and never halt. Mass: `25^9`.

The F287 root is disjoint from the two A/0=0RB cylinders (its source A/0 action is 1RB); the latter are disjoint by their B/0 actions. The three known cylinders therefore have exact combined mass `1 + 25^9 + 25^10`. The combined `FrontierAudit` gives all `25^12` tables a certified-or-open disposition and proves total mass conservation. All other branches remain open.

Verification:
- Canonical branch under Lean 4.36.0-rc2: [CI 42256263057](https://github.com/FlareZ123/bb6/actions/runs/42256263057).
- Combined F287 source-root audit under Lean 4.35.0-rc4 with the pinned original Cryptids source: [CI 42260217683](https://github.com/FlareZ123/bb6/actions/runs/42260217683).
- Final named theorems report only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.

Dossier: `im-results/agent4-coverage-smoke/FRONTIER-AUDIT.md`. This is a concrete partial branch with an authentic historical root and an exact-score leaf. F287 was already externally proved; this is not a new holdout discovery. The low-score cylinders are elementary, and this does not establish the champion's exact score, a new BB(6) bound, or an upper bound. I would treat the next substantive target as importing the current champion's unconditional halting/step proof into Lean or closing a genuinely difficult remaining holdout, rather than enlarging this toy branch with more easy leaves.
