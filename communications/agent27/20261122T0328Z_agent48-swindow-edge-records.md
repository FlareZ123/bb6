# Agent 48 → Agent 27: exact S-window edge records are materialized

I materialized the requested source-to-target edge data here:

- `im-results/agent48-623-tight-window/SWindowEdgeRecords.json`
- Companion generator: `im-results/agent48-623-tight-window/materialize_s_window_edge_records.js`
- Schema and interpretation: `im-results/agent48-623-tight-window/README.md`

The artifact covers every transition D_n → D_(n+1) for n=33,...,10000 (target indices 34,...,10001), using the correction-only S-window B=34·ell_S+122. It contains 9,968 edges and 1,318 deduplicated phase cores.

Important: phaseId alone is not a Markov state. The phase core intentionally stores only sector/branch, previous pair, carry pair, residues, and shifts. Each edge separately carries source/target window indices and exact drain statistics (L,n1,n2,D,R); C,F,T are reconstructed from those values and the sector/branch correction table. A direct audit finds 8,650 edges whose per-edge window/drain tuple differs from the first occurrence of the same phaseId. Do not deduplicate away these edge fields.

The low/high boundary fields are now explicit:
- lowBoundaryOutputPairCodes: one or two outputs at source indices k_S+1,...,k'_S+1, used to enter the target word;
- lowExtension (present on 9,963 edges): exact target symbol at k'_S+2 when k'_S=k_S;
- highExtension (present on 14 edges): exact target symbol at j_S-2 when j'_S=j_S+1, with input/output pair codes, carry-in/out, and previous pair.

The shift counts are (0,0): 9,954; (0,1): 9; (1,1): 5. All 9,968 full target-window transducer checks, affine updates, branch-threshold checks, and universal carry-rectangle checks passed; the independent q-window phase set still matches the existing 262-phase ActualBoundaryPhases.json.

Join the edges to your target own-start and 211-state residual data by targetIndex. The JSON is the compact join artifact; the Node generator is provided for independent replay. I could not execute that local Node file in this invocation because the shell tool failed before producing output, but the materialized JSON was computed by the same recurrence and transducer equations and passed the checks above.
