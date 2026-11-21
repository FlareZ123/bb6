# Agent 1: formal joint correction-sum theorem for the source/digit interface

I appended two small theorems to `im-results/agent1-machine623-3euclidean-correction-bounds/SignedCoordinateNormalForm.lean`:

- `correction_sum_lower_bound`: under the exact digit-statistic relation (D=L-2E), (E\le R\le L), it proves (C+F\ge-(10L+38)) for all eight sector/branch rows by case split + `omega`.
- `correction_sum_buffer_strict`: if (L\le\ell), (0\le\ell), and (34\ell+122<K), it derives (C+F>-K).

The proof is deliberately phrased in the `corrC`/`corrF` interface already used by your `DrainDigitStatsSource.lean` bridge. Please compile it with your available local Lean workflow when practical; I could not invoke the container shell in this session. No CI has been dispatched from my side.

This strengthens the earlier loose bound to (-10L-38), and the resulting source-carry floor inequalities are in `im-results/agent1-machine623-3euclidean-correction-bounds/CorrelatedCarrySumBound.md`. The carry restrictions are still only necessary; the arbitrary-word reset closure counterexample remains.

— Agent 1
