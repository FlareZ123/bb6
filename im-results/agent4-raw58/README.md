# Raw58 E1=0RA parent: five-residual frontier

## Parent and current theorem

The parent cylinder is the six-hole partial machine

`1RB---_1RC---_0RD---_1LD1RE_---0RA_------`

with (25^6=244,140,625) compatible completions. Its first undefined transition is A1, queried after seven transitions.

The source-verified composition in `Raw58MoreCut2.lean` proves:

`∀ m, compatible parent m → WeightedBound 374 m ∨ residual(m)`

where `residual(m)` means compatibility with exactly one of the following five A1-child cylinders:

| A1 move | Next undefined query after executing A1 |
|---|---|
| `0LE` | E0, at step 8 (slot 8) |
| `0LF` | F0, at step 8 (slot 10) |
| `0RF` | F0, at step 8 (slot 10) |
| `1LE` | E0, at step 8 (slot 8) |
| `1LF` | F0, at step 8 (slot 10) |

This is a complete, disjoint five-residual partition at weighted bound 374; it is **not** yet a complete closure of the parent.

## Source-accepted layers

1. `Raw58Cut.lean` (CI run [45520713972](https://github.com/FlareZ123/bb6/actions/runs/45520713972)): the initial A1 partition bounds 13 of 25 first-hole cylinders at 55, leaving 12 five-hole children.
2. `Raw58MoreCut.lean` (CI run [45521202017](https://github.com/FlareZ123/bb6/actions/runs/45521202017)): adds complete child bounds for A1=0RD (120), 1LC (156), and 1RE (93), reducing the residual frontier to nine.
3. `Raw58MoreCut2.lean` (CI run [45596841950](https://github.com/FlareZ123/bb6/actions/runs/45596841950)): adds A1=0RC (167), 1LA (284), 1LB (223), and 1RF (374), reducing the frontier from nine to five.

The final source audit compiled 280 Lean modules. The `#print axioms` profile for `parent_dichotomy` contains only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; the workflow also rejects `sorryAx` and `native_decide`.

## Reusable counter certificates

- `Raw58PairCounter.lean` and `Raw58PairCases.lean`: paired-digit binary countdown; carry skips zero pairs, clears positive digits, and grows the word by one pair at overflow.
- `Raw58BlockCases.lean`: width-3/4 countdown instances.
- `Raw58UnaryDrain.lean`: affine unary-drain returns.
- `Raw58M1391.lean`: alternating C/E sweeps with return recurrence (k\mapsto 3k+10).
- `Raw58OddRun.lean` and `Raw58RD1892.lean`: additional literal-table counter certificates.

These are reusable leaf-level nonhalting arguments, not claims that an entire parent cylinder is nonhalting.

## Next computation: close the five residuals

The next query for each of the five remaining A1 choices is known exactly: E0 for 0LE/1LE and F0 for 0LF/0RF/1LF, all at step 8. The current probe uses weighted cutoff 7014.

- `more.json` contains the five new child specifications (LE, LF, RF, LE1, LF1).
- `generate_more.py` now optionally searches the existing FAR-code bank and one-/multi-block pump candidates automatically; unresolved leaves are printed rather than silently treated as covered.
- `Raw58MoreCut3.lean` composes the five child certificates into a complete parent bound if all five are discharged.
- CI target: `raw58-more3`, run [45601806558](https://github.com/FlareZ123/bb6/actions/runs/45601806558), currently in progress at this checkpoint.

If automatic classification leaves open tables, first try the existing exact/extension-compatible custom tables in PairCases, BlockCases, UnaryDrain, OddRun, M1391, and RD1892. Do not promote the five-residual partition to a complete parent closure until the new source audit passes.

## Reproduction and status

Use `.github/workflows/agent10-four-hole.yml` targets `raw58-cut`, `raw58-more`, `raw58-more2`, and `raw58-more3`. The checked Lean source closure is authoritative; generator output or finite simulation alone is not a proof.

This remains an intermediate research result in `im-results/`. It does not change the global canonical roster count until a complete parent closure is source-checked and grafted into the common quotient roster. BB(6) remains unresolved.
