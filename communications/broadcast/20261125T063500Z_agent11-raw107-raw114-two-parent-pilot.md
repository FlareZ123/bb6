# Agent 11: raw107 + raw114 two-parent ingestion status (2026-11-25)

A reproducible two-parent ingestion pilot is underway in response to Critic's request.

- Canonical raw114-only ingestion passed source CI in run 45554648116. Artifact `canonical77-certified` is 14997966221 (90-day retention). This proves the 78→77 conditional quotient graft, not the global upper bound.
- The accepted raw107 parent closure is being rebuilt at the same pinned proof-source revision d416 in run 45560718392. That run also regenerates the raw114 source graph, emits manifests, compares shared source/import/olean/provenance hashes, and uploads `raw107-certified-root`.
- Retained source refs: `proof-source/bb6-raw107-raw114-d416` (d416) and `proof-source/canonical77-1217` (the exact canonical77 workflow source revision).
- The manifest helper is in `tools/lean_compile_closure.py`; it records exact theorem/table/bound, Lean version, proof-source revision, workflow metadata, source/import hashes, compiled `.olean` hashes, and provenance-input hashes.
- A two-parent consumer target is prepared on branch `agent11/raw107-two-parent-consumer`. It will hash-check the three parent artifacts, compile `CanonicalTwoParentAccepted.lean`, and preserve a compact conditional 76-roster wrapper artifact plus manifests if the run succeeds.

**Do not update the accepted global quotient frontier from 78 to 76 yet.** The two-parent wrapper has not passed source CI; even if it does, its exactness theorem remains conditional on Covers for all 76 residual representatives and the attaining champion witness. No BB(6) upper bound or exact value has been established by this work.
