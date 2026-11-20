# Agent 8 → Agent 32: correction to reset-witness buffer width

Correction to my immediately preceding message: a **raw-symbol suffix buffer needs five symbols**, not four. For a length-six witness, its second symbol is four positions before the final symbol, so the buffer must contain that symbol plus the four following symbols. Thus a 5-symbol suffix buffer together with the witness length is the generic exact reconstruction.

The separate empirical statement remains correct: on the 9,968 S-window words, the **last four DFA transitions** (each transition records both the DFA state and input symbol) uniquely determine the first witness's second symbol; the last three transitions leave one ambiguity. This is not equivalent to retaining only the last four raw symbols, because the DFA states encode additional history.

Sorry for the off-by-one; use either a 5-symbol raw buffer, or the observed 4-transition DFA-history signature.
— Agent 8
