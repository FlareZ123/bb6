# Raw47 D1 sibling: first-hole canonical cut

Parent: `1RB---_1RC---_0RD---_1LD0RC_------_------` (D1=0RC), one of the eight D1 siblings of the authentic `firstOneCylinder` path.

## Deterministic cut preflight

The exact classifier is reused from `im-results/agent7-raw49/cut.cpp` (no new simulation semantics). Parameters: cap 1000, lookback 32, canonical split depth 2. A JS port was used only to preflight and emit the data; it reproduces the known Raw49 reference count (125 open leaves) before applying the same algorithm to Raw47.

Raw47 output: **114 open five-hole residuals**, 131 translated-cycle leaves, 12 split nodes, 32 canonical aliases, no last-hole leaves; latest first-hole query time 10 and latest cycle end 267. The open list is retained verbatim in `Raw47-open.txt`, and the tree in `Raw47-cut.json`. This is computational evidence only until the Lean source audit passes.

## Lean theorem

`generate.py` instantiates `Raw47Cut.template` as `Raw47Cut.lean`. The exact partial table and full first-hole/canonical tree are encoded as a `PartialAudit`. Its intended result is the conditional local refinement:

`TNFQuotientCompatible parent m -> WeightedBound 7014 m OR m lies in one of the 114 explicit canonical residual cylinders`.

It is **not** a parent Cover, does not establish a BB(6) upper bound, and does not remove a global residual until the source-level root consumer is updated. The cut leaves are deliberately retained; no unmatched node is discarded.

## Reproduction

Run the pinned `im-results/agent7-raw49/cut.cpp` with parent above and parameters `1000 32 2`, then run `generate.py`. A future FAR5/translated-pump pass may replace only leaves with independently checked certificates; all others must remain unresolved.
