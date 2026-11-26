# q0 sibling-scan index 33: direct residual closure

**Status:** the isolated two-sided automata certificate and `Cover` leaf passed focused Lean 4.36.0-rc2 CI run [45789439603](https://github.com/FlareZ123/bb6/actions/runs/45789439603). The parent-level original-source Coq consumer is now running in [45789737554](https://github.com/FlareZ123/bb6/actions/runs/45789737554). This is an intermediate local result, not a global q0 closure or a BB(6) upper bound.

## Exact post-decider residual

The existing q0 sibling scan reports one open leaf at active index 33:

`1RB1RD1RC0RE0LA---1LA1LD0LF0RB1LF0LC`

The sole unassigned transition is **C1**; the other eleven entries are fixed. This is the already-produced residual, not a new enumeration of the four-hole parent.

## Formal nonhalting certificate

The exact table already occurs as `R33L0` in `im-results/agent5-weighted-tnf-queue/Q0OpenAutomata.lean` and as key `R33L0` in `q0-open-automata.json`. Its table string is identical to the residual above.

`Q0Index33Automata.lean` isolates that one finite certificate instead of importing the full 94-leaf automata roster. It imports `TwoSidedAutomata`, checks the two finite stack relations and every represented transition (`checked`), and obtains `NeverHalts` through `BB6.Agent4Automata.never`. No bounded simulation or macro conjecture is a premise.

`Q0Index33MinimalHalt.lean` now proves:

- `residual_never`: every total machine compatible with this partial table is nonhalting;
- `residual_weighted_bound B` for every natural-number bound `B`;
- `residual_cover B : Cover (WeightedBound B) residual`, a genuine proof-carrying leaf covering the entire one-hole cylinder.

This is stronger than the earlier 25-to-1 minimal-slice reduction: the automata invariant proves that even the completion assigning **halt** to C1 never reaches that entry. Therefore all 25 completions are covered by one leaf at every weighted bound.

## What this does and does not close

The local residual cylinder is now covered mathematically: the focused Lean source closure compiled 15 modules and checked `residual_never`, `haltCompletion_never`, and `residual_cover`; the reported axioms are `propext`, `Classical.choice`, and `Quot.sound`, with workflow checks rejecting `sorryAx` and `native_decide`. The parent is q0 active index 33, exact table `1RB1RD_1RC0RE_0LA---_1LA1LD_---0RB_------`, four holes, `maxHalt = 156`, weighted bound 162. Its deterministic coarse/automata tree has 985 nodes, 41 first-hole splits, 55 MITM leaves, 140 terminal leaves, and one open leaf (R33L0). The shared original-source workflow is now compiling the exact Coq consumer for offset 33; run 45789737554 is pending. This result does not close the entire q0 root family, the canonical64 roster, or BB(6).

## Independent computational observation

`verify_macro.py` remains a reproducible cross-check, not a proof premise. It replays the blank-run base case and 5,050 macro transitions for 1 ≤ j ≤ k ≤ 100 (1,455,800 simulated transitions). The observed checkpoints are:

- state F, head `H = 2k + 3 - 4j`;
- a singleton 1-marker at `-2k` and a contiguous 1-block on `[H, 2k+2]`;
- for j < k, the next checkpoint is reached in `8j+20` moves;
- for j = k, the next cycle checkpoint is reached in `4k+34` moves.

These observations motivated the original pilot but are no longer needed for the formal nonhalting result.

## Files

- `Q0Index33Automata.lean` — isolated `R33L0` two-sided automata certificate.
- `Q0Index33MinimalHalt.lean` — exact residual nonhalting theorem and weighted `Cover` leaf.
- `verify_macro.py` — independent deterministic simulation/replay only.
