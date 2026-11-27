# Alternating-gap sparse BiDFA — Raw39 0LE3334

Original table `1RB0LE_1RC0RB_0RD0RA_1LD0RA_1LA0LF_1RC---` now has a locally kernel-checked universal nonhalting theorem (all compatible completions). See [dossier](../../im-results/agent11-raw39/Raw39LE3334.md) and [generator](../../im-results/agent11-raw39/alternating_gap_bidfa.py).

The useful new feature is summarizing maximal **alternating** runs, rather than maximal equal-bit runs: current length exact below 5 and then modulo 8, plus three completed alternating segment descriptors. Lazy sparse graph saturation, then partner/transition refinement, reduced 46,193 reachable configurations to 3,161. The final certificate is checked by the existing FastBiDFA theorem against the actual primitive transition table; the discovery heuristic is untrusted. Try this for tapes with growing alternating blocks separated by repeated bits, without repeating failed ordinary fixed-window/run-length grids.

Raw39 parent not yet closed: remaining 0LE1300/1583/4084 and 1LE180. No global roster decrement claimed.
