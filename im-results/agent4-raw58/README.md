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

## Current residual-closure attempt (2026-11-25)

The accepted `Raw58MoreCut2.parent_dichotomy` still leaves exactly five A1 children after the 374-bound partition: `0LE`, `0LF`, `0RF`, `1LE`, and `1LF`. The target closure is at weighted bound 7014.

### Current evidence

- The `0RF` child now has a complete 1346-bound source-accepted certificate: CI run [45636997573](https://github.com/FlareZ123/bb6/actions/runs/45636997573). Its seven custom counter witnesses are part of the checked child source.
- `LE` index 56 is assigned to `Raw58LE56.lean`. Its two-bit block counter constructs arbitrarily long live prefixes and `Raw58Live.never_of_live` lifts the result to every compatible completion.
- `LF` index 157 is assigned to `Raw58LF157.lean`. Its four-bit block counter proves the same kind of unbounded live-prefix property. The `more.json` entry now imports this module.
- The LE56 and LF157 mappings are candidate leaf discharges until the complete source audit below succeeds. The generator's `zipCheck` is the compatibility gate; a wrong leaf index cannot silently close a cylinder.
- The latest candidate census recorded 5,020 open leaves across the five children: 4,552 reused FAR witnesses, 346 fixed n-grams, 76 sweep witnesses, two late single-hole cases, seven 0RF custom witnesses, two recursive counter cases, four sparse wide n-grams, and nineteen run-length relations. The 19 run-length parameter sets are now included in `more.json`; the generator checks them against each exact open table and emits the `TwoSidedAutomata` Lean certificates. The generator also tries the reusable sparse width-23 n-gram checker on remaining unclassified leaves, so the four previously observed sparse candidates are now tested through the same reproducible path. Twelve candidate leaves remained unresolved at the earlier checkpoint. These counts describe candidate ingestion, not accepted proof coverage.

### Child audit and full parent closure

The first full `raw58-more3` attempt, run [45659821185](https://github.com/FlareZ123/bb6/actions/runs/45659821185), was deliberately cancelled after it had regenerated the LE and begun LF. It did not reach the complete generator/Lean audit and provides no closure evidence.

The generator has since been improved: all 19 RLE parameter sets are ingested, auto-classification skips explicitly assigned automata/ngram/custom leaves, and the sparse width-23 checker is applied to remaining unclassified leaves. A targeted `raw58-child` audit for `LF` is now running as [45663400144](https://github.com/FlareZ123/bb6/actions/runs/45663400144). This is a child-level test of the new ingestion path, not a parent closure.

Once the individual child data are fully covered, rerun the existing `raw58-more3` target to compile `Raw58MoreCut3.all_completions` against the original source closure. No complete Raw58 parent closure is claimed until that full audit succeeds and its final axiom profile is inspected.

### Global-roster handoff

The parent is `BB6.Agent4Raw58Cut.parent = BB6.Agent4Raw58RE.p58`, defined by the first four entries of the root path followed by `E1 = 0RA`. It is a distinct sibling of the already-used `p107` and `p114` E1 branches. Agent47 has been asked to check exact membership in the accepted raw114-grafted canonical77 roster and whether an empty-replacement graft is valid. This is only a membership lead: no canonical roster count has changed, and the parent theorem is not yet source-accepted.

Use the existing `raw58-cut`, `raw58-more`, `raw58-more2`, `raw58-more3`, `raw58-rc`, and `raw58-child` targets in `agent10-four-hole.yml`. The checked Lean source closure is authoritative; generator output, finite simulation, and local counter proofs alone are not a global closure. Keep this work in `im-results/` until a genuinely publishable mathematical result is established. BB(6) remains unresolved.
