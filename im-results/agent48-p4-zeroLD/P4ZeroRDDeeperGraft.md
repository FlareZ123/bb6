# P4 deeper branch: E/0 = 0RD, six D/0 fresh-ray children

**Status:** source-level Lean draft; not yet locally compiled, CI-accepted, or integrated into the global manifest.

## Five-step entry

From blank tape, the P4 prefix A/0=1RB, B/0=1LC, C/1=0RD, D/1=1RE followed by E/0=0RD reaches D at head 3. The tape has a marked cell at 1, but every cell at or to the right of head 3 is blank. This is a valid fresh-right entry.

## Six D/0 children

| D/0 action | Macro from D on blank | Length | Shift |
|---|---|---:|---:|
| 0RD | D | 1 | +1 |
| 1RD | D | 1 | +1 |
| 1RE | D,E | 2 | +2 |
| 0RA | D,A,B,C,D,E | 6 | +4 |
| 1RA | D,A,B,C,D,E | 6 | +4 |
| 1RB | D,B,C,D,E | 5 | +3 |

All macros return to D at a strictly greater head position, have nonnegative intermediate head positions, and leave the right half-tape blank. The entry prefix has a fresh right ray, so EntryMacroOracle transfers each macro to the actual blank-root run.

Each child fixes six transition slots and leaves six arbitrary, so each contains 25^6 = 244,140,625 nonhalting complete machines. The six children are pairwise disjoint by D/0 action.

## Frontier effect

These children lie under the still-open P4 E/0=0RD branch and are added to agent48P4DeeperAudit by agent48P4ZeroRDDeeperAudit.

Adding them to the previous expected report pair gives:

- decided: 40,570,883,544,921,875
- open: 19,033,761,230,468,750

The total remains 25^12 = 59,604,644,775,390,625.
