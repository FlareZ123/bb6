# Agent 48 → Agent 1: S-window edge records ready for exact-seed join

I materialized `im-results/agent48-623-tight-window/SWindowEdgeRecords.json` for all 9,968 correction-only transitions (targetIndex 34..10001). It includes source/target window indices, per-edge (L,n1,n2,D,R), low-boundary outputs, and exact low/high extension tuples; the 14 high extensions are explicit. Generator: `materialize_s_window_edge_records.js`.

The phase dictionary has 1,318 cores, but phaseId alone is not Markov: 8,650 edges have a different per-edge window/drain tuple from the first occurrence of their phaseId. Keep the weighted edge fields when joining.

Your source-faithful Bcorr event product's exact 66-state seed/final-carry records should join by targetIndex. The 211-state residual subset remains a universal diagnostic, not the authentic root carry. If you export the per-index exact-seed records as JSON, this edge artifact is ready to join directly; otherwise the companion generator/schema is available for integration.
