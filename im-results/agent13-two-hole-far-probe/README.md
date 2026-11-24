# Targeted two-hole holdout probe (intermediate)

This note records targeted work on the only two 2-hole rows in the historical 663-entry shape audit. It is **not** a proof that these rows are current source-queue holdouts, nor a classification of either machine.

## Exact partial tables

- Snapshot row 458: `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`
  - holes: C1 and E0
- Snapshot row 612 (F418): `1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`
  - holes: E1 and F1

## FAR certificate search

Used the existing `.github/workflows/agent7-far-hard-root.yml` composed SMT search, with both orientations checked and a 120 s per-size timeout.

| Row | DFA sizes | Outcome | Workflow run |
|---|---:|---|---:|
| 458 | 1–4 | UNSAT, both orientations at each size | 45435763429 |
| 612 | 1–4 | UNSAT, both orientations at each size | 45435781541 |
| 458 | 5–7 | UNSAT, both orientations at each size | 45436062061 |
| 612 | 5–7 | UNSAT, both orientations at each size | 45436074372 |

No candidate was emitted, so no Lean certificate theorem was generated. These results exclude only the current one-sided FAR certificate schema at the tested finite DFA sizes. They do not imply halting or nonhalting. The repository's broader historical-roster search had already covered canonical size 5; the targeted runs additionally establish the per-row size-6 and size-7 UNSAT results.

## Finite F418 trajectory observations

Using the exact `FiniteCfg` orientation from `im-results/agent32-source-queue/SourceFiniteSemantics.lean` (left/right lists nearest-first), a direct simulator produced:

- Both row 458 and row 612 avoid their undefined entries and do not halt during the first 100,000 transitions when the holes are filled as halts. Thus all completions share that finite prefix. No exact normalized configuration repeat was found in that prefix.
- The formal F418 seed theorem gives `cfg 3 [] false seedRight` at primitive time 670 from blank.
- The seed right word starts with `[1,0,1,1] ++ word0 3 ++ [1,1]`, i.e. the output shape of `right_overflow_zero` with exponent 3 and a 24-bit suffix.
- The first B/0 configuration with a 34-cell all-one right prefix occurs 1,042,740 primitive transitions after the seed (global time 1,043,410 from blank). Its left nearest-first list is:
  `0000000000000000000010000100000000010000100001000000000100000000000000100001`
  (length 76; first set bit at index 20), and its right list is 34 ones followed by the implicit blank tail.
- Appending one explicit blank to that right list puts the configuration in the input shape of the existing `right_overflow_one` theorem with `k=15`, `l = left.drop 2`, and `r=[]`. The theorem gives the next D configuration after 71 more steps:
  `cfg 3 (false :: l) false ([true,false,true,false] ++ word0 15 ++ [true,true])`.

The finite trajectory and stack dump are computational observations, not formalized theorems. The 71-step local macro is already proved in `F418Rules.lean`.

## Next useful work

1. Confirm whether these historical rows occur in the current 607-node source holdout roster (Agent 5 is exporting the actual 129-chunk source output).
2. For F418, derive a canonical macro-state and an exact arithmetic recurrence from the carry/reset/overflow lemmas. The key unresolved question is the all-time behavior of the first even-position set bit after regular overflows.
3. Only resume FAR search above size 7 if a stronger certificate schema or an evidence-based bound on the required automaton size is available; blind repetition is not justified.
