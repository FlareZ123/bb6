# Tree126 final one-hole sweep recurrence

Target `1RB1RF_1RC1LF_0RD0RF_1LD1RE_---0LB_0RE0LA`, tree126 path `[[10,17],[1,23]]`. This was the sole candidate left after the warm-started FAR search described in [Agent 7's batch dossier](../agent7-far/DepthEightBatch.md).

In head-inclusive zipper notation (left reversed), define A(n) = (A, empty, 0101(11)^n) and B(n) = (A, 1(11)^n, 01011). The blank reaches A(0) in 9 steps. The exact recurrence is:

- A(n) -> B(n), 20n+22 steps. For n>0 the first 20-step block opens the left blank, writes two ones, and moves right two cells. The remaining n-1 blocks repeat the 20-step local sweep; the 22-step terminal block turns at the right blank.
- B(n) -> A(n+1), 11(2n+1) steps. Each 11-step block consumes one left one and appends one right one to the 010 prefix.
- Thus A(n) -> A(n+1), 42n+33 steps, with net head displacement -1. All local runs use only assigned transitions, including E1 but never E0. Iteration supplies arbitrarily long defined blank-origin prefixes for every completion of E0.

[Final126.lean](Final126.lean) encodes this proof with the existing openRun/sweepR/sweepL lemmas, and exports the intended universal never and weighted leaf. The fixed traces and parameterized list algebra were checked locally in Lean 4.36.0-rc2 against a small interface harness (the imported sweep lemmas in the harness were assumptions); full original-source compilation is required before reporting kernel acceptance of the entire leaf. A paper proof follows directly from the three displayed finite local sweeps and induction. No universal BB(6) conclusion follows yet.

After original-source acceptance, graft this leaf at the specified tree126 address, retaining the other branches. Do not repeat the FAR search for this table.

## Roster overlap correction

Exact slot-by-slot cross-match against all four BlockPumpData files found this table already present as [Agent50 table92 / cert92](../agent50-weighted-tnf-pilot/BlockPumpData4.lean). The independent direct recurrence above provides a shorter mathematical description and alternative proof, **not a new unique residual closure** relative to the canonical 124 roster. The original Agent7 dossier tracked FAR search coverage rather than the union of all proof methods. Do not decrement the canonical frontier count for this result. Any accepted alternative can be used to replace the existing certificate if useful, but do not duplicate integration work.

Full original-source Lean verification succeeded in [CI 45512885605](https://github.com/FlareZ123/bb6/actions/runs/45512885605). As corrected above, this is an alternative proof, not a new unique frontier closure.
