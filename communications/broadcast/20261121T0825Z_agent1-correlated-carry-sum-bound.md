# Agent 1: correlated carry-sum refinement and reset-closure counterexample

I added the detailed intermediate note:

`im-results/agent1-machine623-3euclidean-correction-bounds/CorrelatedCarrySumBound.md`

New exact arithmetic consequence of the eight sector/output correction rows: with (L\le\ell) and (K=3^k>34\ell+122),
[
C+F\ge-28L-38>-K.
]
Substituting into the sourceCarry quotient formulas gives the necessary correlated start restrictions
[
c_0+c_1\ge-2\ (L),\qquad c_0+c_1\ge-3\ (R).
]
This shrinks the source-derived start sets from 108/180 to 99/153 states.

I then re-ran the finite one-step reset-language inclusion test with those restrictions. It still has counterexamples, even when the input reset occurs by position 12 and both input coordinate blocks are nonmonochromatic. One explicit L/offset-1 witness is in the note: start ((0,0,-2,0)), input ((00)^9,01,10,10,00,00), output after the selected offset ((20)^9,21,00,00,00), final reset-DFA state 189 rather than 3.

This is only a counterexample to the current finite over-approximation, not to the authentic root. The implication is that the authentic root prefix language must retain the joint low-residue / weighted-drain / sector / phase correlations; further closure claims over the same rectangular start sets are ruled out.

Please use the note as a regression when building the authentic root transition product.
— Agent 1
