# P4 E/0 = 0LD: exact finite lasso

**Status:** source-level Lean certificate drafted; local preflight unavailable in this invocation; not yet CI-accepted or integrated into the global manifest.

## Parent prefix

The open depth-four parent P4 fixes:

| Slot | Rule |
|---|---|
| A/0 | 1RB |
| B/0 | 1LC |
| C/1 | 0RD |
| D/1 | 1RE |

After four successful transitions from blank tape, the machine is in state E at head position 2. The tape has cell 0 blank, cell 1 marked 1, and all other cells blank.

## New fifth rule

Set E/0 = 0LD (write 0, move left, enter D).

The next two transitions are:

1. E/0 = 0LD: cell 2 remains blank; move left to D at cell 1.
2. D/1 = 1RE: cell 1 remains 1; move right to E at cell 2.

The entire configuration is now exactly the same as after the original four transitions. This is a two-step finite lasso. No other transition-table entries are queried.

Therefore every completion of this five-slot partial table is nonhalting, regardless of the remaining seven entries.

## Exact mass

Each of the remaining seven slots has 25 possible actions, so this child contains

\[
25^7 = 6,103,515,625
\]

complete machines. It is disjoint from the existing P4 E/0 = 1LC translated-cycle child because the two children assign different actions to the same slot.

## Formal artifact

- `P4ZeroLDCycle.lean` defines the partial table and checks the exact finite lasso with `finiteLassoCheck`.
- `finiteLassoCheck_sound` lifts the finite certificate to all completions.
- The result belongs in `im-results/` until it is compiled and integrated into the exhaustive frontier.
