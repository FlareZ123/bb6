# P4 eight-child exact graft

**Status:** source-level Lean draft. The 0LD finite-lasso certificate is in P4ZeroLDCycle.lean; this file adds five fresh-ray children and one halt child. Not yet locally compiled, CI-accepted, or integrated into ResidualFrontierManifest.

## Parent and existing graft

The open depth-four P4 parent fixes:

- A/0 = 1RB
- B/0 = 1LC
- C/1 = 0RD
- D/1 = 1RE

The existing agent27GraftedAudit closes E/0 = 1LC by a translated finite-support cycle.

After the four fixed moves from blank tape, the machine is in E at head 2, reading blank 0, with all cells at and to the right of the head blank.

## New exact children

The P4EightChildGraft.lean source adds these seven certificates to the existing 1LC child:

| E/0 action | Certificate | Macro length | Net head shift |
|---|---|---:|---:|
| 0LD | exact finite lasso | 2 | 0 |
| 0RE | fresh ray | 1 | +1 |
| 1RE | fresh ray | 1 | +1 |
| 1RB | fresh ray | 4 | +2 |
| 0RA | fresh ray | 5 | +3 |
| 1RA | fresh ray | 5 | +3 |
| halt | exact halting prefix | — | — |

The fresh-ray macros start from E on blank tape. Their intermediate head positions are all nonnegative, their final state is E, their final head is strictly right of the start, and their right half-tape is blank. The four-step entry from blank reaches E on a fresh right ray, so EntryMacroOracle transfers each macro to the actual blank-root run.

The 0LD child is the exact step-4/step-6 configuration repeat. The halt child halts when E/0 is queried after the four fixed prefix transitions.

All seven new children assign distinct actions to E/0, so they are pairwise disjoint and disjoint from the existing 1LC child. Each child leaves seven transition slots arbitrary and therefore has mass 25^7 = 6,103,515,625.

## Frontier delta

The existing report pair is:

- decided: 40,570,837,402,343,750
- open: 19,033,807,373,046,875

Adding the seven new children gives the expected pair:

- decided: 40,570,880,126,953,125
- open: 19,033,764,648,437,500

The total remains 25^12 = 59,604,644,775,390,625. Within the P4 parent, eight of 25 E/0 children are now decided (the existing 1LC plus the seven additions), leaving 17 children open.

This report delta is an exact cylinder-mass calculation; the source artifact still needs Lean compilation and an audit-report proof before it can be promoted or included in the global manifest.
