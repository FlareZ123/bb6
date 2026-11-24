# P4 deeper exact children: E/0 = 0LC

**Status:** source-level Lean draft; not yet locally compiled, CI-accepted, or integrated into the global manifest.

## Six-step blank entry

Start from the P4 parent rules A/0=1RB, B/0=1LC, C/1=0RD, D/1=1RE. Assign E/0=0LC. The six-step blank entry is A/0, B/0, C/1, D/1, E/0, C/1. It clears cells 0, 1, and 2, reaching state D at head 2 on an entirely blank tape.

## Ten D/0 children

From D at head 0 on blank tape, the following macros are checked. The actual six-step entry places D at head 2, so the macros transfer to the real run.

| D/0 action | Certificate | Macro length | Head shift |
|---|---|---:|---:|
| 0LD | translated finite support | 1 | -1 |
| 0LA | translated finite support | 7 | +1 |
| 0RA | fresh right ray | 7 | +3 |
| 1RA | fresh right ray | 7 | +3 |
| 1RB | fresh right ray | 6 | +2 |
| 0RD | fresh right ray | 1 | +1 |
| 1RD | fresh right ray | 1 | +1 |
| 1RE | fresh right ray | 3 | +1 |
| 1LD | fresh left ray | 1 | -1 |
| halt | halts at the entry configuration | 0 | — |

The translated checks compare the complete finite marked-cell support after translation; they do not require the intermediate head to stay to the right of its start. This is important for 0LD and 0LA, whose paths move left of the entry head.

The right-ray macros return to D at a strictly greater head position, have nonnegative intermediate head positions, and leave the right half-tape blank. The D,E,C macro for 1RE writes then clears the starting cell and clears the next cell. The 1LD child is the leftward counterpart: D/0 writes 1 and moves left into D again, leaving a pristine left ray at every successive entry. The entry configuration itself has a completely blank left ray. The halt child stops immediately after the six-move blank entry.

Each child fixes six transition slots and leaves six arbitrary, so each contains

\[
25^6 = 244,140,625
\]

complete machines. The ten children are pairwise disjoint because they assign different actions to D/0.

## Frontier effect

These children lie under the still-open P4 E/0=0LC branch and are added to agent48P4EightChildAudit by agent48P4DeeperAudit.

Adding all ten to the expected P4 eight-child report pair gives:

- decided: 40,570,882,568,359,375
- open: 19,033,762,207,031,250

The total remains 25^12 = 59,604,644,775,390,625.
