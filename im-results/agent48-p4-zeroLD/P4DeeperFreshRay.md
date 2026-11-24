# P4 deeper fresh-ray children: E/0 = 0LC

**Status:** source-level Lean draft; not yet locally compiled, CI-accepted, or integrated into the global manifest.

## Exact six-step entry

Start from blank tape with the P4 parent rules:

- A/0 = 1RB
- B/0 = 1LC
- C/1 = 0RD
- D/1 = 1RE

Assign E/0 = 0LC. The six-step blank entry is:

1. A/0 writes 1 at 0, moves right to B.
2. B/0 writes 1 at 1, moves left to C.
3. C/1 clears cell 0, moves right to D.
4. D/1 preserves cell 1, moves right to E.
5. E/0 = 0LC clears cell 2, moves left to C.
6. C/1 = 0RD clears cell 1, moves right to D.

The resulting configuration is state D at head 2 on an entirely blank tape.

## Three D/0 children

From D on blank tape:

| D/0 action | Macro | Length | Shift |
|---|---|---:|---:|
| 0RD | D | 1 | +1 |
| 1RD | D | 1 | +1 |
| 1RE | D,E,C | 3 | +1 |

For 1RE, the macro writes 1 at the initial cell and moves to E; E/0=0LC clears the next cell and returns left to C; C/1=0RD clears the initial cell and returns right to D. The entire tape is blank again at the new head.

All three macros have nonnegative intermediate head positions, return to D at a strictly greater head position, and leave the right half-tape blank. EntryMacroOracle therefore lifts them to the six-step entry. The remaining six transition slots are arbitrary, so each child contains

\[
25^6 = 244,140,625
\]

nonhalting complete machines.

## Frontier effect

These are three disjoint children of the still-open P4 E/0 = 0LC branch. They are added to agent48P4EightChildAudit by agent48P4DeeperAudit.

Adding all three to the expected eight-child report pair gives:

- decided: 40,570,880,859,375,000
- open: 19,033,763,916,015,625

The total remains 25^12 = 59,604,644,775,390,625.
