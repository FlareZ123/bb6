# F421: one-hole Raw139 holdout

The standard blank-start table is `1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---`, initial state A, sole unassigned F1. The canonical representative in `im-results/agent8-coverage-contract/LedgerTextRows.lean` has order FDAEBC, root C, no reflection. This is the open E0=1LD,A1=0LC branch of the Raw139 seven-hole audit, distinct from its source-proved neighbors.

## Strongest current reduction

[FrontierTransduction.md](FrontierTransduction.md) gives the exact D-to-D word return; F1 is reached precisely on a bad 111 parse. [CarryCountdown.md](CarryCountdown.md) derives the principal two-return phase and strict regular binary countdown. [BoundaryEpoch.md](BoundaryEpoch.md) extends it to **complete regular drains with terminal P-run deletion**, exact primitive cost, and a **secondary binary countdown** in the exceptional tail. This consists of three boundary macros and three regular drains, with explicit prefix and positivity premises. The far-to-near drain recurrence avoids expanding any number of terminal collapses.

The local arbitrary-precision engine reached 10^50 principal macros (exactly 28573549291907737747121673600169498036340127855568021245374953124058438783837935224986696975611208306 primitive moves) without F1. A full-drain run reached odd macro 5000 with exact 1245-bit cost. The secondary tail at odd 190 has 15 cells and marker integer 32750. The autonomous primary-prefix recurrence and closed tail formulas then check all 32750 secondary decrements, crossing the zero-marker boundary at odd 65690. Exact general arithmetic continues through odd 65710 without F1; this exposes a new nonterminal-collapse regime. The remaining mathematical target is all-time closure of these higher-level boundaries. This is paper-level conditional mathematics and finite computation, not an all-time machine verdict, Lean acceptance of the new results, or BB(6) lower bound.

## Reproduction

- `frontier_map.py`: exact bit-word formula, compared against 1000 primitive returns (711352 steps).
- `compressed.cpp`, `carry.cpp`, `test_compressed.py`: earlier bounded-integer run compression and strict carry skip (10^18 macros, exactly 2741467853641781568730607840197912170 moves).
- `boundary.py`: arbitrary-precision whole-drain and secondary arithmetic; commands and proof premises in BoundaryEpoch.md.
- `F421Frontier.lean`: original-machine frontier reduction source; its presence does not establish acceptance of the new countdown theorems.
- `state-1b.json`, `state-2b.json`: independent finite primitive checkpoints.
- `prefix.cpp`, `cross_zero.py`: autonomous prefix recurrence and secondary-zero crossing, see BoundaryEpoch.md.
- `search_far.cpp`: earlier size-six FAR search; [FARIncremental.md](FARIncremental.md) and `far_incremental.cpp` extend exhaustive exclusion to reachable canonical DFA sizes 1–8 in both orientations. No FAR witness; this does not rule out larger automata.
