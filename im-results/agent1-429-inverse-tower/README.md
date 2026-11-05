# BB429 parameterized inverse tower

Agent 1, 2026-11-05. Intermediate formal method result. The blank-root machine #429 and BB(6) are unresolved.

Source: [BB429InverseTower.lean](BB429InverseTower.lean). For any positive u,t and any n, theorem `inverse_tower` constructs genuine length-4n accelerated paths ending respectively at `(16u+9,16u+17+16^(n+1)t)` and `(16u+17,16u+25+16^(n+1)t)`. The proof uses an exact alternating pair of four-step source-transition schemes and induction on n. The companion `arbitrarily_deep_terminal_9` constructs an arbitrarily long finite source path from a synthetic start ending on `b+1=2a` with `a%8192=9` (one choice: `a=16^(n+4)+9`). **These starts are not proved reachable from the true blank seed.** The theorem establishes a limitation on fixed-depth reverse search, not a machine-wide decision.

Lean 4.36.0-rc2 local compilation used exact copies of the actual BB429Rank next/run/run_add definitions and gave only standard axioms `[propext, Classical.choice, Quot.sound]` with no sorry. A manual proof audit imports the original repository module; [run 41969922656](https://github.com/FlareZ123/bb6/actions/runs/41969922656) was queued at writing. Only after successful CI should this be called unchanged-source certified.

Agent 4 separately constructed stronger same-residue halting synthetic inputs for arbitrary dyadic modulus (see `im-results/agent4-bb429-dyadic-barrier/`). Agent 33 excluded entire genuine-root terminal cylinders 4105 and 6153 modulo8192. The inverse tower has a different explicit quartet grammar, but no external novelty has been assessed. Root-sensitive forward ancestry is needed to eliminate all surviving candidates. File retained in im-results as an intermediate.
