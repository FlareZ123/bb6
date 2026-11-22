# Paired-carry synchronizing-language automaton

## Result

Starting from the full 66-state paired-carry set, the exact image-subset automaton has **211 reachable subsets**. Every nonempty digit-pair word maps the full 66-state set to a subset of size at most 8.

The subset-size distribution is:

| Image size | Reachable subsets |
|---:|---:|
| 1 | 66 |
| 2 | 78 |
| 3 | 30 |
| 4 | 21 |
| 5 | 6 |
| 7 | 6 |
| 8 | 3 |
| 66 | 1 (the initial full set) |

All 66 singleton subsets are reachable. The image-subset automaton is complete under all nine digit-pair symbols.

Minimizing the DFA with acceptance condition 'the image subset is a singleton' gives a **41-state complete DFA**. All 66 singleton subsets merge into one accepting state. Its shortest accepted words have length 2; the six shortest words are 01·20, 01·21, 01·22, 12·00, 12·01, and 12·02 (symbol encoding x,y ↦ 3x+y).

## Interpretation

The 41-state DFA recognizes exactly the words that synchronize the 66-state paired-carry closure: after reading such a word, the resulting paired-carry state is independent of the initial state in that closure.

This is a post-reset automaton. It applies after the full-range reset step has entered the 66-state closure; it does not replace the 263-state full-range reset recognizer and does not by itself establish that authentic root windows contain synchronizing suffixes.

## Reproducibility

- Source: [PostResetCarryPairClosure.json](../agent49-parity623/PostResetCarryPairClosure.json)
- Generator: [compute_pair_carry_sync_dfa.js](compute_pair_carry_sync_dfa.js)
- Certificate: [PairCarrySynchronizingSubsetDFA.json](PairCarrySynchronizingSubsetDFA.json)

The certificate includes all 211 subset states and transitions, shortest representatives, the stable partition into 41 Myhill–Nerode classes, and the minimized transition table. The generator verifies quotient well-definedness after partition refinement.

This is an exhaustive finite computation against the committed 66-state transition table, not yet a Lean-certified theorem.
