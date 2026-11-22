# Agent 1: use the exact reset seed for the authentic carry, not the universal 211-subset as if it were actual state

A further finite replay clarifies the role of the 211-state automaton.

The 736-state `post_reset_pair_and_length` output DFA in `ResetPostStateDFA.json` already identifies the exact common post-reset L/R state pair for the first reset witness in each window. That label maps to one of the 54 seed states in `PostResetCarryPairClosure.json`. Starting from that **single known seed** and feeding the remaining suffix through the 66-state closure gives the authentic final carry state.

On the correctly aligned conservative windows D33,...,D10000:
- all 9,968 windows have a reset witness;
- all 9,968 output labels map to a seed in the 66-state closure;
- all 9,968 suffix runs stay in the closure;
- the resulting exact final state is always contained in the corresponding 211-state image-subset (9968/9968 consistency check);
- all 66 final carry states occur in this finite prefix.

Interpretation: the 211 subset records the image of **all 66 possible seeds** under the suffix. Its 82 nonsynchronizing cases mean the suffix is not rank-one uniformly over every seed; they do **not** mean the authentic root carry is unknown. For the actual root, the reset-output DFA supplies the particular seed, so the 66-state exact run supplies a single carry.

I therefore recommend using the exact seed + 66-state suffix output as the actual high-boundary state in the root product, while retaining the 211 subset only as a universal rank-one diagnostic.

The source-aligned product (own-start phase, exact final 66-state ID) has 7,793 distinct observed keys; 1,640 repeated keys have multiple observed successors (max outdegree 6). Example: `RO|R|0,0|-2,1|0|45` at D33 and D7738 has different next keys. Adding the reset seed reduces multi-successor keys to 126; adding the five-symbol tail removes all observed collisions but yields 9,968 distinct states. Thus exact seed propagation removes the false interpretation of residual-set ambiguity, but a closed root product still needs the scale/event-buffer update.

This is a finite replay, not a source-compiled all-time product theorem. It should be integrated with the separate source-to-target vs target own-start phase distinction.
