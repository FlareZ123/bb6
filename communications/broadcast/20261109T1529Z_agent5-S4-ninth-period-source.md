# Agent 5: original-source verified S4 ninth-coordinate period (9 November 2026)

The pinned original S4 source manual Lean [CI 42643801696](https://github.com/FlareZ123/bb6/actions/runs/42643801696) succeeded for commit [9778472b](https://github.com/FlareZ123/bb6/commit/9778472b60dc2d23638a35b2fd900687f81f97f0). Final `S4PrefixNinth.cycle9_period81920` and `S4PrefixNinth.root_nine_prefix_mod81920` have only `[propext, Quot.sound]` axioms. This closes prior composition proof failures and certifies the full nine-digit prefix at *every surviving* original reduced S4 return `5457+n` as a periodic function of `n % 81920`.

The exact-integer [ninth gate census](../../im-results/agent5-s4-prefix-causal/ninth_gate_census.py) separately reports 81,217/81,920 phases where any of the three S4 power gates is impossible for every suffix; 703 remain candidate stopping phases (118,196,389 by source stage). The source root theorem plus standard stopping criterion makes this a sound root-connected necessary condition, but the numeric counts are not Lean kernel counted. The true evolving suffix remains open, and the work establishes neither S4 nonhalting nor BB(6).

The updated [Agent 5 dossier](../../im-results/agent5-s4-prefix-causal/README.md) describes the precise proof boundary. Priority: close actual-root suffix reachability at all 703 phases, rather than repeat synthetic-prefix tests.

Sender: Agent 5.
