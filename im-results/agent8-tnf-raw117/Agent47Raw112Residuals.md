# Raw112 E1=1LC: exact final two residual leaves

**Status:** empirical exploration only; neither residual has a proved Cover or a nonhalting theorem. The parent partial audit is at weighted bound 100,000.

Parent:
`1RB---_1RC---_0RD---_1LD1RE_---1LC_------`

The Agent47 deterministic generator `im-results/agent47-raw112-cut/generate.py` emits `FAR 13287 unresolved 2` and the following exact one-hole residual tables:

1. `1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---0LE`
2. `1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---1RB`

They agree on A–E and differ only in F1; F0 is the sole undefined transition in each. The original-source compile workflow 45575393941 successfully generated these tables and began compiling the Lean closure, but the GitHub runner received a shutdown signal at 08:35:47Z while compiling `Raw112Sparse30Row10`. This was an infrastructure termination, not a Lean diagnostic; the source audit must be retried.

## Empirical simulation

A direct two-symbol sparse-tape interpreter was run on both partial machines with F0 left undefined.

- Both first enter state F at step 118, after first taking A1 at step 117.
- Neither reads F0 during the first **100,000,000** steps.
- Consequently, every one of the 25 possible F0 completions (halt plus 24 write/move/next-state transitions) shares this entire 100-million-step prefix.
- The 25 completions of each residual also all exceeded 100,000 steps in a separate bounded enumeration.

| Residual | State after 100M | Head position | Number of 1s | Visited head interval |
|---|---:|---:|---:|---:|
| F1=0LE | B | -3,006 | 4,307 | [-6,922, 68] |
| F1=1RB | C | -86 | 5,892 | [-7,064, 68] |

These are computational observations, not proofs of nonhalting or eventual halting. The two machines have already diverged at step 118, so the different long-run states and tape densities are expected.

## Mathematical obligation

To close the E1=1LC parent at target (B), prove `Cover (WeightedBound B)` for each residual. The useful fact is that F0 is not consulted in the first 100M steps; a successful recurrence proof may therefore be independent of the F0 completion if it establishes that F0 is never reached. Otherwise, the proof must cover all 25 F0 completions.

Prioritize finding a translated configuration, macro-step recurrence, counter invariant, or a proof that the F0 transition is unreachable. Reuse the existing `Raw112CounterBase`, `SweepPumping`, `Raw112Sparse*` and symbolic certificate infrastructure; do not repeat the 25^6 parent enumeration or the 100M scan without a new mathematical hypothesis.
