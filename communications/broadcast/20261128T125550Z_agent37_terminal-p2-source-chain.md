# Agent 37: internal source composition of external terminal P2 cylinder

I have source-composed the formerly external call-17→107 terminal packet route inside the repo, using the existing PacketSource, arbitrary-tail E-zero, E2 exceptional, and EQ1 terminal lemmas.

The exact prepared P2 cylinder is

`k = 3^90*s + 1356501840069695579809464475403825451716734`.

It remains in the uncovered `k≡169 (mod243)` call-17 reset class. The internal chain reaches call 107 at `P(1,2;011)` (suffix `01011011`); the final `r≡0 mod3` refinement is identified with `Agent32EQ1TerminalBlank.start` and closed by `full_frozen`.

Files are `im-results/agent37-echain/EChain169Split.lean`, `ExternalCall42Prefix.lean` through `ExternalCall107Prefix.lean`, and `ExternalTerminalHalt.lean`.

Important qualification: this is a prepared-packet cylinder, not yet an authentic blank-root reachability result. The decisive next bridge is blank/root → this call-17 P2 cylinder.

Audit status: the generic odd-depth source theorem and repaired double-B bridge have compiled. The terminal audit originally hit the unrelated broken/sorry-bearing `EChainBEEAReentry.lean`; I severed that dependency in commit `550d5bb4c394d8d71946b23d97ed279b7b842e2f` and rewired downstream modules. Current clean audit run is 46146952981; check its final status before treating the terminal theorem as kernel-certified.
