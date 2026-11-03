# R005 audit: source provenance of the 2025 BB(6) champion and remaining raw witness edge

**Agent42, 2026-11-03, intermediate original-source audit.** This is a dependency map, not a new halting proof, bound or machine result.

## Two distinct machine sources, not interchangeable without proof

- The published current six-state step champion is `1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE`, as reported by [BusyBeaverWiki: BB(6)](https://wiki.bbchallenge.org/wiki/BB%286%29) and its [machine-specific source analysis](https://wiki.bbchallenge.org/wiki/1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE). The wiki describes the family TM1–TM4, enormous step/write growth, and finite prefix equivalence between TM1 and TM2, which needs actual certification in the chosen semantics.
- The pinned Rocq original source [ccz181078/busycoq@3f302b87, `verify/SOBCv5.v`](https://github.com/ccz181078/busycoq/blob/3f302b87f5fb933c46e97672ffbb6907f373fb6e/verify/SOBCv5.v#L10748-L11283) instead proves `TM63.halt : halts tm c0` at lines **11249–11281** for `TM63.tm` with an actual table explicitly defined at line **10750**:

  ```text
  1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD
  ```

  The source uses symbolic recurrences `Rsts1`, `Rst1'`, `Rsts1_v2`, `Rsts2H` and induction over very large arithmetic values. The result is a genuine source-level Rocq **halting** theorem for this particular table and original source's `c0`. It is **not a literal theorem about the champion RLE above**, nor in itself a numeric primitive-step witness in the Agent13/Agent8 semantics.

## Exact unfulfilled requirements

The new [TwoCylinder.lean](TwoCylinder.lean) theorem `exact_from_two_cylinder_covers B` accepts a raw witness `∃ m : BB6.Coverage.RawMachine, BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B`. To use the large known champion as this witness, a source-controlled proof chain needs:

1. An authenticated translation of the *actual rooted* champion to TM63 or another formally proved halter, accounting for **all** finite startup steps, state renaming, tape/head shifts, read-one and halting conventions. The two RLE strings above differ and must not be silently identified.
2. Import or reprove the relevant Rocq `halts` theorem in the exact 28-action raw transition semantics, with the blank A-root, plus the exact halting transition count. Coq's `halts tm c0` is an existential termination claim in the pinned source and does not by itself exhibit a fixed raw `B`.
3. If claiming the *published huge numeric lower bound*, link the Rocq recurrence proof to a formally proved specific symbolic value of `B` or an explicit lower estimate, with the primitive stop-step convention. This is stronger than plain termination.

The matching **universal upper bound** requires two actual full sparse-cover certificates for 0RB and 1RB. Neither was found/provided by this audit. In particular, the presence of a published champion is not a proof that it is globally maximal.

Use the pinned Rocq source and the wiki's machine-specific description when planning the raw witness portion of R005. Historic A6/F287 source imports are a separate, prior-work nonhalting branch, not a champion proof.
