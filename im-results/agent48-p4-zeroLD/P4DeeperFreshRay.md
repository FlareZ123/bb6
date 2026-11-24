# P4 deeper fresh-ray child: E/0 = 0LC, D/0 = 0RD

**Status:** source-level Lean draft; not yet locally compiled, CI-accepted, or integrated into the global manifest.

## Exact six-step entry

Start from blank tape with the P4 parent rules:

- A/0 = 1RB
- B/0 = 1LC
- C/1 = 0RD
- D/1 = 1RE

Assign E/0 = 0LC. The first five transitions reach C at head 1 reading 1; C/1 = 0RD then reaches D at head 2. The six-step tape is entirely blank:

1. A/0 writes 1 at 0, moves right to B.
2. B/0 writes 1 at 1, moves left to C.
3. C/1 clears cell 0, moves right to D.
4. D/1 preserves cell 1, moves right to E.
5. E/0 = 0LC clears cell 2, moves left to C.
6. C/1 = 0RD clears cell 1, moves right to D.

The resulting configuration is state D at head 2 on an entirely blank tape.

## Fresh-ray rule

Assign D/0 = 0RD. From state D on blank tape, this rule writes blank, moves right one cell, and remains in D. The next cell is blank, so the same rule repeats forever. The macro has length 1, displacement +1, and never moves left of its starting head.

The six-step entry plus this one-step fresh-ray macro is checked by finiteEntryMacroCheck and lifted by finiteEntryMacroCheck_sound. The remaining six transition slots are arbitrary, so the child contains

\[
25^6 = 244,140,625
\]

nonhalting complete machines.

## Frontier effect

This is a deeper child of the still-open P4 E/0 = 0LC branch, not one of the eight E/0 children already decided by agent48P4EightChildAudit.

If added to the expected eight-child report pair, the new pair is:

- decided: 40,570,880,371,093,750
- open: 19,033,764,404,296,875

The total remains 25^12 = 59,604,644,775,390,625.
