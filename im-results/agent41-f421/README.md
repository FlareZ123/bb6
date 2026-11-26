# F421: one-hole Raw139 holdout

## Exact target

The standard blank-start table is `1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---`, with initial state A and single unassigned instruction F1. The family ledger identifies this rooted member as F421; its canonical representative appears in `im-results/agent8-coverage-contract/LedgerTextRows.lean` with state order FDAEBC, canonical root C, and no reflection.

It is the unresolved E0=1LD, A1=0LC branch of the seven-hole Raw139 parent in `im-results/agent41-raw139-small/Raw139SmallPair.lean`, distinct from the source-proved E0=1LD, A1=0LE neighbor and E0=1LA sweep closure.

## Strongest current reduction

[FrontierTransduction.md](FrontierTransduction.md) gives the exact D-to-D return map: F1 is reached precisely by a bad 111 token in the left parser. [CarryCountdown.md](CarryCountdown.md) derives a new two-return principal phase, a binary countdown on regular tape cells, and a closed-form transition count over whole countdown intervals. The regular-cell safety lemma is independent of the untouched suffix. The remaining mathematical obligation is the exceptional boundary behavior when the marker value becomes zero or a cell degenerates.

The C++ implementation (`compressed.cpp`, `carry.cpp`) evaluated 10^18 principal macros, representing exactly **2741467853641781568730607840197912170 primitive transitions**, without reading F1. The largest single skipped block was 2^56-1 macros. The calculation was cross-checked with the unaccelerated word formula on 12,000 examples and the per-macro engine through 20 million macros. See the derivation for reproducibility and proof boundaries.

This is a finite safe prefix, not a source-accepted Lean theorem, a proof of nonhalting or a new BB(6) lower bound. The missing F1 completion halts only if that row is eventually reached.

## Earlier independent evidence

The original primitive blank-start simulator completed 2 billion transitions without reading F1. Complete tape checkpoints are `state-1b.json` (state D, head 88184, visited [-69,89969], 45013 ones) and `state-2b.json` (state B, head 119870, visited [-69,124107], 62084 ones). The nearly alternating tape motivated the pair-run representation. `frontier_map.py` compared the first 1000 word returns with primitive simulation (711352 steps).

FAR searches through canonical DFA size 6 did not supply a witness. `search_far.cpp` and the existing manual `.github/workflows/agent41-raw139-small.yml` preserve the size-six search and its checker. These finite failures do not establish impossibility of a larger FAR invariant.

## Research target

Close the exceptional odd-epoch and carry-degeneration dynamics, or find the first unsafe token and establish its exact primitive cost. The regular-cell reduction is a starting point for that proof. `F421Frontier.lean` contains original-machine frontier lemmas; this file's existence does not itself establish source acceptance of the new countdown reduction.
