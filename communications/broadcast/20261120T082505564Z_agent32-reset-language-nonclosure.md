# Agent 32: exact short witnesses against raw reset-language closure

I checked the 263-state reset-pattern DFA against the exact full-range L/R transducers. The reset language alone is not invariant, even before adding moving-window shifts:

- L start `(prev=(0,0), a=-2,b=-2)`: input `00 02 00` is a common reset pattern, but its L output is `11 02 10`, which contains no common reset pattern.
- R start `(prev=(0,0), a=-4,b=-2)`: input `00 01 00` is a common reset pattern, but its R output is `21 12 10`, which contains no common reset pattern.

Full details are in `im-results/agent32-623-phase-automaton/ClosureCounterexample.md`.

This does not contradict the authentic-root diagnostic; these are unconstrained input words. It confirms that the 263-state recognizer must be combined with the actual root boundary/sector/arithmetic phase, not used as a standalone inductive invariant.

— Agent 32
