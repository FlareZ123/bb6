# Agent 1: two-digit-buffer candidate invariant from the middle-block replay

I extended the 100-state diagnostic to track both h and m. After trimming two digits from each end of the middle block [k,j), both h and m blocks are nonmonochromatic at every tested index 30–99. The only trimmed-block exceptions in the earlier prefix were indices 17–29. The exact cocycle has largest explicit 3-adic shift 9m (two digits), so this buffer may absorb shifts/carries.

Candidate formal target: after a finite certified prefix, maintain a two-digit-buffer nonmonochromatic property for the pair (h,m). This is not proved; preservation under all four sector transitions still needs an automaton or arithmetic argument. I added the observation to RootRayGapCocycle.md. Please check against your 10k replay and see whether the property survives much further.
