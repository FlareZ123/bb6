# Framed macro-step finite automata reduction

A finite certificate establishes nonhalting of a partial two-symbol machine, for **every compatible completion**, by combining adaptive local computation trees with a two-ray automaton invariant. This is a strengthening of the primitive-step FAR certificate construction already used in the repository; no claim of priority over the published literature is made.

## Theorem

Represent the tape by two nearest-first words with infinite zero padding. A configuration is (q,L,R). A finite automaton consists of a DFA for the left ray, read far-to-near, and an NFA for the right ray, read near-to-far, with start node indexed by the left DFA state and machine state. Its accepting language is an overapproximation of bad configurations. The left blank state must be stable under zero, the NFA's zero-suffix acceptance set must be a fixed point of zero-predecessors, and its halt node must accept all suffixes.

For each q, a finite binary prefix tree inspects left and right symbols. Its leaves either reject a prefix (the corresponding bad-language path must reach the halt node) or specify an exact positive-length local run from a known prefix pair (L,R) to (L',R') in state q'. Local runs are forbidden from reading outside the known frame. For every possible DFA state d of the untouched left tail and every NFA node t, require

```
path(R', node(pushWord(d,L'),q'), t)
    implies path(R, node(pushWord(d,L),q), t).
```

If the blank configuration is outside the bad language, then the machine never halts, for every compatible completion.

Proof: the local run frames over arbitrary untouched tape tails. The path implication gives backward closure of the bad language for each exact macro transition. The prefix tree covers both rays including their implicit zeros; zero-padding invariance permits finite word representatives of unequal length. Thus each safe configuration admits a positive-length safe macro. Iterating gives arbitrarily long actual live prefixes; every intermediate ordinary time is live as well. No search heuristics are assumed by the theorem.

## Formalization and first application

Source: [certificate and generator](../../im-results/agent32-macro-far/README.md). The generic theorem and finite bitmask checker are kernel-checked. The original-source bridge uses the existing FAR representation theorem and establishes `BB6Coverage.MacroFARBridge.never`. Its first application is the raw59 A1=0LB leaf 693:

```
1RB0LB_1RC1LB_0RD0LA_1LD1RE_1RF1LA_---1LC
```

Four-state left DFA `001213333` (first digit denotes orientation), maximum local horizon six, 75 NFA states. The generated certificate proves the missing F0 transition is never used, for all 25 possible completions. [Original-source CI](https://github.com/FlareZ123/bb6/actions/runs/45546616573) passed with the standard axiom audit (no sorry or native_decide). This is an individual cylinder certificate, not a global upper-bound proof. It is available for ingestion into raw59's remaining 0LB branch.

Unlike a primitive-step automaton, one framed macro preserves correlations across internal backtracking: the left abstraction is applied to the same untouched tail before and after the entire local computation. This is the mechanism enabling certificates with different accepted invariants.
