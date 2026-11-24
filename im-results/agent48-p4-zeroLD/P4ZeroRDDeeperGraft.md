# P4 deeper branch: E/0 = 0RD, nine D/0 children

**Status:** source-level Lean draft; not yet locally compiled, CI-accepted, or integrated into the global manifest.

## Five-step entry

From blank tape, the P4 prefix A/0=1RB, B/0=1LC, C/1=0RD, D/1=1RE followed by E/0=0RD reaches D at head 3. The tape has a marked cell at 1, but every cell at or to the right of head 3 is blank. This is a valid fresh-right entry.

## Nine D/0 children

| D/0 action | Certificate / macro | Length | Shift |
|---|---|---:|---:|
| 0RD | fresh right ray: D | 1 | +1 |
| 1RD | fresh right ray: D | 1 | +1 |
| 1RE | fresh right ray: D,E | 2 | +2 |
| 0RA | fresh right ray: D,A,B,C,D,E | 6 | +4 |
| 1RA | fresh right ray: D,A,B,C,D,E | 6 | +4 |
| 1RB | fresh right ray: D,B,C,D,E | 5 | +3 |
| 0LB | translated finite support | 5 | +1 |
| 0LE | exact finite configuration lasso | 2 | 0 |
| halt | halts at the five-move entry configuration | 0 | — |

The six fresh-ray macros return to D at a strictly greater head position, have nonnegative intermediate head positions, and leave the right half-tape blank. The entry prefix has a fresh right ray, so EntryMacroOracle transfers each macro to the actual blank-root run.

For 0LB, the five-step macro D,B,C,D,E returns to D one cell right and translates the entire finite marked-cell support: the original mark at offset -2 is cleared and the new mark is at offset -2. For 0LE, the two-step D,E sequence returns to the exact same D configuration. These checks use the full finite support, not only the head position. The halt child stops immediately after the entry prefix.

Each child fixes six transition slots and leaves six arbitrary, so each contains 25^6 = 244,140,625 complete machines. The nine children are pairwise disjoint by D/0 action.

## Frontier effect

These children lie under the still-open P4 E/0=0RD branch and are added to agent48P4DeeperAudit by agent48P4ZeroRDDeeperAudit.

Adding them to the ten-child E/0=0LC report pair gives:

- decided: 40,570,884,765,625,000
- open: 19,033,760,009,765,625

The total remains 25^12 = 59,604,644,775,390,625.
