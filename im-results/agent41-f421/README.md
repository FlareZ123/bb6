# F421: one-hole Raw139 holdout

The standard blank-start table is `1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---`, initial state A, sole unassigned F1. The canonical representative in `im-results/agent8-coverage-contract/LedgerTextRows.lean` has order FDAEBC, root C, no reflection. This is the open E0=1LD,A1=0LC branch of Raw139.

## Strongest current reduction

[FrontierTransduction.md](FrontierTransduction.md) gives the exact D-to-D word return; F1 is reached precisely on a bad 111 parse. [CarryCountdown.md](CarryCountdown.md) derives the principal two-return phase and strict regular binary countdown. [BoundaryEpoch.md](BoundaryEpoch.md) extends it to complete regular drains with terminal P-run deletion, exact primitive cost, and a secondary binary countdown. [PrimaryGuard.md](PrimaryGuard.md) gives a conditional inductive guard for the secondary phase, including the authentic 32750 decrements from odd 190 to 65690. The secondary-zero crossing creates a different nonterminal-collapse regime.

**New tertiary phase:** [TertiaryEpoch.md](TertiaryEpoch.md) derives the two-odd/one-even cycle and proves an inductive primary guard even with arbitrary terminal head deletions. At the genuine odd-65700 seed the new marker integer is 2^8214−1; all primary and tail budgets hold for that entire countdown. The conditional induction yields a safe frontier through odd principal macro 65700+2(2^8214−1), with the subsequent regular drain. The zero boundary requires symbolic head evolution. The arithmetic lemmas in TertiaryGuard.lean compile locally with standard axioms; full original-source bridge and authentic-seed formal acceptance remain open.

This is a paper-level conditional finite-prefix theorem, supported by exact arithmetic and randomized frontier comparisons. It is neither a whole-machine verdict nor a BB(6) bound improvement. The next mathematical target is the tertiary-zero crossing or a higher-level all-time closure, rather than a longer finite replay.

## Reproduction and dependencies

- `frontier_map.py`: exact bit-word formula, compared against 1000 primitive returns (711352 steps).
- `compressed.cpp`, `carry.cpp`, `test_compressed.py`: strict carry skip, 10^18 macros and exact primitive count 2741467853641781568730607840197912170.
- `boundary.py`: arbitrary-precision whole-drain and secondary arithmetic; 10^50-macro exact safe prefix and odd-5000 primitive cost recorded in BoundaryEpoch.md.
- `prefix.cpp`, `fast_prefix.cpp`, `cross_zero.py`, `verify_tertiary.py`: autonomous prefix recurrence, byte-identical secondary-zero checkpoint, new tertiary seed and exact-cycle checks.
- `F421Frontier.lean`, `F421Regular.lean`, `F421Drain.lean`, `F421Odd.lean`, `PrimaryGuard.lean`, `TertiaryGuard.lean`: frontier, regular-budget and arithmetic proofs; distinguish local copied-model checks from original-source closure. General terminal-deletion drain and higher-level composition still require source formalization.
- `state-1b.json`, `state-2b.json`: independent finite primitive checkpoints.
- [FARIncremental.md](FARIncremental.md), `far_incremental.cpp`: exhaustive exclusion of reachable canonical FAR DFA sizes 1–8 in both orientations; larger automata remain open.
