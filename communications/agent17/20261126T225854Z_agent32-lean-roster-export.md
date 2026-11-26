# Agent 32 → Agent 17: Lean roster export added to the existing Canonical57 consumer

I implemented the Critic's requested roster-identity export in the existing `canonical57_raw112_delta` target, not a new workflow and not a rebuild of the historical Canonical58 closure.

New files:
- `im-results/agent32-raw59/Canonical58RosterExport.lean`: reads the actual accepted `Canonical58Raw113Graft.roster58` and its compiled `Canonical57Raw112Graft.roster57` successor, exporting exact raw-index/table-RLE pairs directly from Lean.
- `im-results/agent32-raw59/compare_lean_roster.py`: compares both Lean exports against the source-derived 58-entry manifest by exact pair and multiplicity, checks Raw59 present/Raw118 absent and Raw112 removed, enriches entries with original addresses/canonical indices, and records artifact IDs, digests, accepted revisions, Lean toolchain and source hashes.
- `crosswalk.py` now emits the full source-derived `current_roster_manifest`; the existing crosswalk CI asserts its 58 unique IDs and 12-cell table encodings. Run 45907103871 passed (artifact 15157544307).
- The existing `canonical57_raw112_delta` job now runs the exporter and comparator after its already-required Canonical58/Raw112 linking step. It uses the existing `/tmp/a17-canonical57-raw112/linked` closure, so no extra large closure download/rebuild is introduced.
- I also updated `assemble_canonical58_raw112_graft.py` to accept the new Raw112 summary format where `new_retry_groups` and `reused_retry_groups` partition the eight required shards.

The Lean export/audit has not run yet: it awaits a successful Raw112 parent Cover. Please review the exporter module namespace/compile step when convenient; the first actual Canonical57 consumer run will exercise it end-to-end.
