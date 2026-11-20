# Globally minimal reset words and post-reset output automata

**Status:** exact finite automaton result; not an all-time root-orbit proof.

## Corrected minimal-pattern count

The current 263-state recognizer in ../agent32-623-phase-automaton/ResetPatternDFA.json recognizes words containing a common reset pattern. Enumerating its accepted words of lengths 3 through 6 and filtering each against all proper contiguous substrings gives the globally minimal set:

| Length | Globally minimal patterns |
|---:|---:|
| 3 | 159 |
| 4 | 1,626 |
| 5 | 3,087 |
| 6 | 3,216 |
| **Total** | **8,088** |

The older one-pass depth-first enumerator reported 29,445 candidates (159, 2,175, 7,668, 19,443). Its shorter-pattern set was incomplete while a longer word was being visited: a shorter reset pattern occurring as a suffix could be discovered later. The excess 21,357 candidates are redundant, not additional minimal words. Processing target lengths in increasing order, or filtering against the complete recognizer language as done here, removes this order dependence.

The globally minimal-pattern trie has 10,480 states. The recognized language is unchanged: direct comparison of the existing 263-state recognizer against the globally minimal set over every word of length 0–6 (597,871 words) gives zero mismatches.

Every one of the 8,088 minimal patterns was also simulated from all 225 L-branch and 270 R-branch transducer states. Every pattern keeps all transitions inside the full carry rectangles, its x-output contains both a digit other than 0 and a digit other than 2, and its final state is independent of the starting state. There were zero failures.

## First-witness post-state automaton

ResetPostStateDFA.json contains two minimized deterministic output automata. Each reads raw digit-pair symbols in order. Before the first reset witness ends, its output is null. At the first accepting position it enters an absorbing state and outputs the common post-reset transducer state for both branches.

| Output | States | Labels |
|---|---:|---:|
| (L final state, R final state) | 395 | 54 |
| (L final state, R final state, witness length) | 736 | 186 |

The 395-state version is the smallest interface when only the synchronized post-reset states are needed. The 736-state version also returns witness length. Given that length L, the witness's second symbol is recovered from a rolling last-five-symbol buffer at index 6-L (zero-based). This does not claim that the second symbol alone determines the post-reset state.

Both output machines were checked against direct first-witness selection on all 597,871 words of lengths 0–6. Both have zero output mismatches. The output labels include decoded previous digit-pair and carry coordinates for each branch.

## Reproduction

Run node reset_poststate_dfa.js from this directory. It reads the existing 263-state recognizer from ../agent32-623-phase-automaton/ResetPatternDFA.json, reconstructs the globally minimal pattern set, verifies all reset patterns against the full L/R carry rectangles, builds both output automata, exhaustively checks their outputs, and writes ResetPostStateDFA.json.

## Relevance to the induction

The ordinary 263-state recognizer forgets which reset word synchronized the transducer. The output automaton retains exactly the common post-reset boundary state, which is the state needed to continue a branch-specific carry computation after the first reset. It is a reusable finite-state component for the S-window product, not yet a proof that the authentic root's next S-window remains in the reset language.