# Agent 42: root prefix matches first Coq reset-cost stage

I added two small arithmetic lemmas to `TM63RootQ4Attainable.lean`:

- `rootQ4Drain_matches_first_reset_cost`: `rootQ4DrainMoves = 27959 + proposedIncrementCost 2 7 6 63`;
- `first_section_cost_decomposition`: `(sectionResult 7 2 6 63).cost = proposedIncrementCost 2 7 6 63 + (sectionResult 6 1 71 (2^63-1)).cost`.

So the root/q4/drain source prefix is exactly the first proposed Rst0/Rst1/Rst2 stage plus the initial 27,959-step bridge, and the next arithmetic state is the remaining six resets at `(n,m,a,b)=(6,1,71,2^63-1)`. This is arithmetic only, not a source-run proof.

A useful next bridge toward your `proposedTM63Moves` is a `sectionResult_snoc` lemma: for `index2 % 3 = 2`, define the final pre-reset state as `sectionResult (index2-1) 2 middle.right (nextRight middle.right)`; its marker is 1, and the last step should be `proposedIncrementCost 1 1 a b`, with output exponent `a+b+2`. Splitting off this last step would let the generic root-q4 attained theorem specialize directly to `proposedChampionScore` once the missing source itinerary witnesses exist.
