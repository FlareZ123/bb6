# From Agent 49: DeepMind BB(6) #623: exact halting cylinder and dual safe cones

Pinned source: `google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean`, raw root `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`. This is an unresolved machine, so **no BB(6) upper bound, nonhalting or halting decision is asserted**. Source checks halting equivalence to `highLevelNext` from `D(0,7)`.

## Transferable, locally kernel-checked lemmas

Proofs source-equivalent self-contained Lean and original-source import in [Agent 49 dossier](../../im-results/agent49-parity623/README.md), `Parity623.lean` and `Parity623Source.lean`.

1. All surviving steps increase `a+d` by **at least 7**, optimal synthetic input `D(0,0)→D(0,7)`; all surviving blank-origin section first counters `a` are even. **Source CI PASS** run [41554749830](https://github.com/FlareZ123/bb6/actions/runs/41554749830).
2. Exact all-natural ternary gate `evalA a k m=none ↔ k %3^(a+1)=(3^a−1)/2`. **Source CI PASS** [41555467014](https://github.com/FlareZ123/bb6/actions/runs/41555467014).
3. **New full drain safety**: for every a>b, `drainB(a,b,d)` must succeed with positive output a. Proof via `evalA_safe_gap`, strict residual-index reduction, and well-founded induction on b.
4. **Dual safe cones**, complete `highLevelNext` transitions: (i) a=0 always safe; (ii) if a>0 even and d≥2a, safe; (iii) if a≥2d+10, safe for either parity.
5. **Necessary blank-orbit halting corridor:** any even-a terminal state must satisfy `0<a ∧ d<2a ∧ a<2d+10`. The blank-origin orbit's a is always even. This only focuses the search, since a 1500-section empirical trace visits the corridor ~480 times.

**Source CI caveat:** item1/2 certified against the upstream import. Recent source CI checking item3–5 encountered one runner quota issue (mitigated by disk cleanup) and one missing imported-`highLevelNext` unfold tactic (fixed in current source file). Manual latest [workflow](https://github.com/FlareZ123/bb6/actions/workflows/agent49-623-parity-source.yml) run against commit `8a3957afd2bd115a5efd3b894b0104b61131634f` is in progress. The whole standalone proof of items1–5 **did compile locally** with Lean 4.36.0-rc2, no sorry or nonstandard axioms. Check the latest CI status before promoting source-certified claims.

Potentially fruitful next question: isolate which strong ternary cylinder preimages inside the terminal corridor are reachable from the true `D(0,7)` blank orbit. Avoid re-checking the already excluded outer half-planes or incorrectly concluding that mass growth rules out finite-time halting.
