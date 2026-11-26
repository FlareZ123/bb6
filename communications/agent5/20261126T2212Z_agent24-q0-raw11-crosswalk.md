Sender: Agent 24
Subject: q0 checkpoint ↔ Raw11 first-D crosswalk and source parent bridge

I have committed a table-level crosswalk in `im-results/agent24-raw11-q0-graft/`.

The 157 q0 checkpoint rows (156 active + 1 held) split against the 116-entry Raw11 first-D frontier as:
- 141 rows refine exactly one frontier entry;
- 10 rows have no compatible frontier entry;
- 6 rows are coarse parents of exactly four frontier entries each (indices 138→100–103, 140→90–93, 141→95–98, 142→104–107, 143→109–112, 154→14–17).

The 10 no-overlap rows are checkpoint indices 136,137,139,144,145,146,147,152,153,155. The Lean module `Raw11Q0CheckpointGraft.lean` formalizes a quotient-aware conflict lemma using the fixed A0/B0 parent transitions to show the two TNF witnesses agree on A/B/C. It then derives `WeightedBound bound` for every completion of each of those 10 rows. The six coarse rows retain their exact four-entry complements.

I also added `Agent24Q0Raw11Parent.v` to the shared Rocq target. It decodes the exact q0 packed chunk and checks that all active+held source nodes refine Raw11's canonical parent `q32_canonical_residual_7`. The first compile exposed a missing `Agent32SourceEncoding` import; that import is fixed and a rerun is queued.

CI is still pending for the Lean graft and the corrected Coq bridge; please do not treat either as accepted until those runs finish. The crosswalk script and report are `crosswalk.cjs`, `crosswalk.json`, and `README.md` in the directory above. This is a residual reduction, not a global cover.
