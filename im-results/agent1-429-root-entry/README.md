# Exact blank-root entry into the #429 J chart

## Mathematical statement

For the explicit complete twelve-slot table `source429`, the blank A-root
executes exactly 35 successful primitive transitions and reaches the
configuration `j00Config`:

- state A;
- absolute head coordinate 3;
- marked cells exactly `[-3,4] ∪ {6}`;
- equivalently, relative to the head, marked cells `[-6,1] ∪ {3}`.

The final tape is the canonical J(0,0) tape. `JRootEntry.lean` records the
complete table (including the D/1 halt), the ordered 35 writes, and the
equality `run source429 35 blank = some j00Config`.

## Evidence and source boundary

The Lean proof is now definitional (`rfl`) once the finite table and the
35-write tape are unfolded. A local Lean 4.36.0-rc2 preflight against the
same `BB6Coverage` operational definitions (`Config`, `run`,
`rawStep`, and `applyMove`) compiles the theorem and reports only
`[propext]`, with no `sorryAx`. This is a local source-equivalent
preflight, **not yet an original-dependency CI certificate**.

The explicit `source429` table still needs a pointwise bridge to the
repository's `BB429PhysicalFrontier.target429` completion and the pinned
original Cryptids machine. Agent 32 has taken that bridge/lift investigation.
The earlier suggestion that `target429` is necessarily a *different
semantic table* was too strong: its sparse-table completion may be
computationally inconvenient while agreeing on every valid six-state slot.
Do not claim the original-source root-entry theorem until the pointwise
identity and physical source transport pass the unchanged-source Lean audit.
The manual workflow is `.github/workflows/agent1-429-root-entry.yml`.

## Why the entry matters

A checked physical blank-root entry would supply the base case for an
all-time J/Junc chart and global head-frontier argument. It turns the chart
problem from an arbitrary prepared-input question into a genuine root
continuation problem.

## Remaining open problem

The 35-step entry does not prove that the subsequent J/Junc orbit stays in
a safe chart, that later C/0 events are global head records, or that #429
never halts. The central remaining task is an all-time physical
frontier/history invariant across every regular and exceptional J/Junc
transition, connected to the actual blank root.

Keep this candidate in `im-results/`. It is not a complete #429 decision,
a BB(6) bound improvement, or a BB(6) solution.
