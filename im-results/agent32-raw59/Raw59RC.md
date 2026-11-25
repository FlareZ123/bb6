# A shared inductive nonhalting proof for two RC residual cylinders

Machines `1RB0RC_1RC---_0RD1LF_1LD1RE_0RA1LA_1RC0LF` (0RC open 228) and `1RB1RC_1RC---_0RD1LF_1LD1RE_0RA1LA_1RC0LF` (1RC open 485) share an infinite family of genuine D-state section returns. Each has only B1 unassigned. The result covers all 25 completions of each partial table.

The compressed Lean source, unpacked with `python unpack_rc.py`, proves `arbitrary_live` for both variants using exact partial zipper moves. Local Lean 4.36.0-rc2 checked the complete theorem with [propext, Quot.sound], using a projection of the original computational zipper definitions. The `Raw59RCBridge.lean` original-machine bridge passed [original dependency closure CI](https://github.com/FlareZ123/bb6/actions/runs/45534189368). Both machines are source-accepted nonhalters.

## Section proof

Both sides are nearest-cell-first finite words, considered up to zero padding. Encode a pair (b,c) as 0^b 1^c. The scan alphabet is A=(1,2), B=(1,6), C=(1,10), D=(1,12), E=(4,6). Trigger symbols include F=(3,6), G=(5,4), H=(5,6), I=(6,2), J=(6,6), K=(9,6), L=(11,2), M=(11,6), and the blank. The left D section has word 10 1^x 0 (x=2 or 4). The scan rules, left-run popping and triggers all quantify over arbitrary untouched finite tape tails. Their concatenation gives `flush_section`, an exact positive-duration return that consumes an arbitrary finite scan prefix and one trigger. The proof works for either value of A1.

The initial machine enters the base-4 section after 53 or 43 steps respectively, then three flushes yield Kphase(1,[]). Kphase(n,w) has base 2 and right word A^n K w. Four flushes take it to Kphase(n+2,u), where u is computed by a finite-state prefix transducer. On an empty tail, u=B. A nonempty tail starts with A or B. The allowed adjacent pairs (start ^ and end $) are:

    ^$ ^A ^B
    AA AB AD AH AL AM
    B$ BI BJ
    D$ DA DB
    H$ HA HB
    IA IB ID IH
    J$
    LA LB LD LH
    M$

The finite-state transducer has five phases; the proof of `tail_closed` uses a finite reachable product-state transition table and structural induction on the tail. It checks all allowed successors and termination; no finite horizon is assumed. `cycle` composes the four flushes, and `live_sections` iterates them with increasing n=2j+1. Thus for every requested time bound there is an actual partial-machine run at least that long. No execution can query B1, regardless of how that hole is completed.

This is an all-time residual decision, rather than a longer simulation or a FAR candidate. It removes the shared obstruction from both RC children. The full 1RC child certificate passed source CI; the full 0RC child has a complete candidate, including a two-pass sweep for its other difficult residual.
