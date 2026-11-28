# Two remaining Raw11 source-root hard leaves reduce to opposite E1-neighbor obligations

**Status:** exact symbolic control-flow reductions (conditional). Neither global nonhalting statement is proved yet. This note isolates the *precise inductive tape invariant* needed to close each leaf and avoids unfocused continuation of 10M–20M-step simulations.

## q0-148, last unclassified F1 slot

Table: `1RB1LC_1RC0RE_0LA0LD_1LA0RF_1RB1RD_0RC---`.

**Sufficient tape invariant:** whenever the blank run enters state **E** reading **1**, the **cell immediately to the right is 0**.

Proof that this suffices: the only assigned transition into **F** is **D1→0RF**. The only transitions into **D** are **C1→0LD** and **E1→1RD**. From C1 the machine writes zero at the cell immediately to the right of the new D head; if the D head subsequently reads 1 and moves right into F, the F head therefore reads **0**, not the unspecified F1. From E1, by the stipulated neighbor invariant, the new D head reads 0, hence takes D0→1LA instead of D1→F. Therefore F1 is never queried; every completion is nonhalting, including the unique completion with a HALT at F1.

In an exact first-2,500,000-step blank simulation E1 occurred **844 times**, with right neighbor 0 every time (sampled E-centered 13-bit contexts only `1010101010101`, `1010101010110` and `1010101010000`). This **does not** prove the invariant.

## q0-151, last unclassified F0 slot

Table: `1RB1LC_1RC0RD_0LA1RD_1RB0RE_1LC1RF_---0RC`.

**Sufficient tape invariant:** whenever the blank run enters state **E** reading **1**, the **cell immediately to the right is 1**.

Proof: the **only** assigned transition entering F is **E1→1RF**. That move puts the F head at the cell immediately to the right of the former E head. By the stipulated neighbor invariant F necessarily reads 1, follows F1→0RC, and never queries unspecified F0. Every completion is nonhalting.

In an exact first-2,500,000-step blank simulation E1 occurred **62,324 times**, with right neighbor 1 every time. Again this is **only computational evidence**.

## Focused proof directions

Both hard machines reduce to a single *state-conditioned two-cell relation at E1*, with opposite prescribed right-neighbor bit. A source-checkable global invariant of reachable tapes establishing the relevant relation (for example a regular-language inductive invariant, symbolic sweeping-phase grammar or a two-stack automaton) would prove a universal `Cover` for the exact one-hole cylinder via the existing `never_of_region` or `Agent4Automata` checker. Direct simulations, narrow finite-window automata, ngram/lag/blk/alt finite-state overapproximations tried so far are insufficient. **Do not claim that the empirical observations establish nonhalting.**

This note is an actionable mathematical reduction, not a published resolution; keep it in `im-results/` until the E1-neighbor assertion has a validated induction proof.
