# #623 buffered phase-automaton work

This directory develops a finite-state induction candidate for the authentic canonical root orbit beginning at (D(0,7)). It is **intermediate research**: no all-time nonhalting theorem or BB(6) result is claimed.

## Current artifacts

- [BranchSelection.md](BranchSelection.md) derives a conditional simplification: once the central (x)-digit block is nonmonochromatic, the exact output-side test (g\ge T) reduces to the sign test (g>0).
- [PhaseAutomaton.md](PhaseAutomaton.md) specifies the moving-window and finite boundary-phase closure problem.
- [reset_patterns.js](reset_patterns.js) exactly enumerates the minimal common reset patterns of length 3--6 for both signed-coordinate carry transducers, builds an Aho--Corasick recognizer, and minimizes it.
- [ResetPatternDFA.json](ResetPatternDFA.json) is the generated 263-state minimal DFA for the language of words containing a common reset pattern.

## Exact finite reset-pattern computation

The transducers use the full initial state sets:
- L: 9 previous digit pairs times (5\times5) carries = 225 starts;
- R: 9 previous digit pairs times (6\times5) carries = 270 starts.

A common reset pattern must, for **every** start of both branches, keep the carry in range, emit an x-output word containing a digit other than 0 and a digit other than 2, and finish in a branch-constant transducer state. The generator keeps only patterns minimal under contiguous-subword containment.

The current exact finite enumeration gives:

| Pattern length | Minimal common reset patterns |
|---:|---:|
| 3 | 159 |
| 4 | 2,175 |
| 5 | 7,668 |
| 6 | 19,443 |
| **Total** | **29,445** |

The Aho--Corasick trie has **34,916 states**, but Moore minimization reduces the complete absorbing-acceptance DFA to **263 states** (partition counts 9, 102, 159, 234, 263, 263). The minimization is exact for the finite trie automaton. The minimized DFA was compared against direct substring membership on all **597,871** digit-pair words of lengths 0 through 6, with no mismatch. The pattern generator visits 98,398 word prefixes. The full carry rectangles are invariant under every digit-pair input; the generator nevertheless checks every transition and fails closed if a carry exits its rectangle.

These are exact finite automaton-construction counts, not a root-orbit theorem. A word containing one of these patterns is synchronizing for both branch transducers, because the pattern collapses every admissible state and sets both nonmonochromatic-output flags; the suffix then preserves those facts.

## Reproduction and next step

Generate the pattern recognizer:

```bash
node im-results/agent32-623-phase-automaton/reset_patterns.js
```

Export the minimal patterns:

```bash
node im-results/agent32-623-phase-automaton/reset_patterns.js --emit-patterns
node im-results/agent32-623-phase-automaton/reset_patterns.js --emit-minimized-dfa
```

Cross-check the existing full-range root diagnostic (this is a reproduction, not a proposed longer scan):

```bash
node im-results/agent1-machine623-3euclidean-correction-bounds/synchronizing_word_scan.js 10000 --emit-blocks \
  | node im-results/agent32-623-phase-automaton/reset_patterns.js --verify-stdin
```

The next mathematical/computational task is to compose this recognizer with the exact current-branch digit transducer and the one-low/three-high moving-window phase, then test finite-state closure from a source-checked prefix. The earlier root scans and short-selector negative tests are sufficient; do not extend the root horizon. If the product graph has a counterexample, preserve it and revise the invariant. If it closes, extract a finite certificate and prove it against the unchanged source definitions.
