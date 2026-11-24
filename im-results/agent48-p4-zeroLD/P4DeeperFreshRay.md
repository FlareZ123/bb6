# P4 deeper exact children: E/0 = 0LC

**Status:** source-level Lean draft; not yet locally compiled, CI-accepted, or integrated into the global manifest.

## Six-step blank entry

Start from the P4 parent rules A/0=1RB, B/0=1LC, C/1=0RD, D/1=1RE. Assign E/0=0LC. The six-step blank entry is A/0, B/0, C/1, D/1, E/0, C/1. It clears cells 0, 1, and 2, reaching state D at head 2 on an entirely blank tape.

## Eight D/0 children

From D at head 0 on blank tape, the following macros are checked. The actual six-step entry places D at head 2, so the macros transfer to the real run.

| D/0 action | Certificate | Macro length | Head shift |
|---|---|---:|---:|
| 0LD | translated finite support | 1 | -1 |
| 0LA | translated finite support | 7 | +1 |
| 0RA | fresh ray | 7 | +3 |
| 1RA | fresh ray | 7 | +3 |
| 1RB | fresh ray | 6 | +2 |
| 0RD | fresh ray | 1 | +1 |
| 1RD | fresh ray | 1 | +1 |
| 1RE | fresh ray | 3 | +1 |

The translated checks compare the complete finite marked-cell support after translation; they do not require the intermediate head to stay to the right of its start. This is important for 0LD and 0LA, whose paths move left of the entry head.

The fresh-ray macros all have nonnegative intermediate head positions relative to their start, return to D at a strictly greater head position, and leave the right half-tape blank. The D,E,C macro for 1RE writes then clears the starting cell and clears the next cell.

Each child fixes six transition slots and leaves six arbitrary, so each contains

\[
25^6 = 244,140,625
\]

complete machines. The eight children are pairwise disjoint because they assign different actions to D/0.

## Frontier effect

These children lie under the still-open P4 E/0=0LC branch and are added to agent48P4EightChildAudit by agent48P4DeeperAudit.

Adding all eight to the expected P4 eight-child report pair gives:

- decided: 40,570,882,080,078,125
- open: 19,033,762,695,312,500

The total remains 25^12 = 59,604,644,775,390,625.
