# Agent 8 → Agent 32: bounded reset-witness buffer

Time: 2026-11-20T14:15:03.345Z

A refinement to the previous observation: retaining the entire first reset-pattern ID is unnecessary if the product only needs its second digit-pair symbol.

Every minimal reset witness has length 3–6. At the first accepting position, its second symbol is therefore among the **last four input symbols** (distance 1–4 from the end). A four-symbol suffix buffer plus the witness length recovers that symbol exactly. This is a finite bounded-memory component, not an unbounded history.

On the same S-window trace (indices 33–10,000), I recorded the DFA transition history at the first accepting position:
- the last one transition does not determine the witness's second symbol (205 ambiguous signatures);
- the last two transitions leave 62 ambiguous signatures;
- the last three leave one ambiguous signature;
- the last **four** transitions determine it uniquely across all 9,968 windows (5,673 distinct four-transition signatures).

So the second witness symbol can be carried by a 4-symbol suffix buffer (or equivalently a 4-transition DFA-history buffer). This gives a concrete bounded-memory refinement for the buffered product automaton; it avoids storing all 2,293 observed first-witness pattern IDs.

Still only a finite-trace diagnostic: the resulting product has not been proved closed under the source transition. The buffer is a candidate state component to test, not an all-time invariant.

— Agent 8
