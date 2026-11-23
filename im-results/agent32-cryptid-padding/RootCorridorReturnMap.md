# Root prefix to the DR corridor family

**Status:** projected finite trace only; not a Lean reachability certificate.

**Correction (2026-11-23):** Agent 12's
`im-results/agent12-cryptid-root-invariant/RootCorridorMacro.md` explicitly
withdraws the proposed full mod-3 return map. In particular, its earlier
q≡1 (mod 3) CR-branch formula was not established and must not be used to
continue this trace. This document preserves only the independently
reconstructed 24-successor prefix from the seven-raw-step root entry to the
first corridor state.
[
D(3,3)=\mathrm{DR}([0,0,0,1],[1,3]).
]
Here every list abbreviates pairs whose second coordinates are zero.

| Macro index | Mode | Left | Right |
|---:|---|---|---|
| 0 | DR | [0,0] | [1] |
| 1 | DR | [0] | [1,0] |
| 2 | DR | [] | [1,0,0] |
| 3 | EL | [0] | [1,0,0] |
| 4 | DL | [0] | [0,0,0] |
| 5 | EL | [0,1] | [0,0] |
| 6 | EL | [0,0,1] | [0] |
| 7 | EL | [0,0,0,1] | [] |
| 8 | CR | [0,0,0,1] | [0] |
| 9 | CR | [0,0,1] | [2] |
| 10 | CR | [0,1] | [4] |
| 11 | CR | [1] | [6] |
| 12 | EL | [0] | [0,9] |
| 13 | EL | [0,0] | [9] |
| 14 | DL | [0,0] | [8] |
| 15 | DR | [0,0] | [1,6] |
| 16 | DR | [0] | [1,0,6] |
| 17 | DR | [] | [1,0,0,6] |
| 18 | EL | [0] | [1,0,0,6] |
| 19 | DL | [0] | [0,0,0,6] |
| 20 | EL | [0,1] | [0,0,6] |
| 21 | EL | [0,0,1] | [0,6] |
| 22 | EL | [0,0,0,1] | [6] |
| 23 | DL | [0,0,0,1] | [5] |
| 24 | DR | [0,0,0,1] | [1,3] |

The first seven transitions are the root-entry trace already stored in
`stack_system_sim.py`; the remaining 17 are the continuation to (D(3,3)).
There is currently no validated return map beyond D(3,3) in this file.
No later checkpoints follow from the 24-step prefix alone.

This is a computational trace of the projected successor clauses. It
does not establish the full pair-stack equations or the original TM run
until each successor is composed from the external Lean mode lemmas.
The withdrawn q≡1 branch must be independently re-derived before any
continuation is treated as evidence.
