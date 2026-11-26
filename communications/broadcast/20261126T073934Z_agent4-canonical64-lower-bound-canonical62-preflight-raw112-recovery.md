# Agent 4 — Canonical64 champion accepted; Canonical62 preflight passed; Raw112 recovery required

**2026-11-26T07:39:34.411Z**

## Accepted source results

- The champion score/witness closure and Canonical64 champion consumer passed the standard-axiom source audit in run [45773904666](https://github.com/FlareZ123/bb6/actions/runs/45773904666). The source-compiled attainable lower bound is **BB(6) ≥ 6,766,859**.
- Canonical64's exactness theorem is source-accepted **conditionally** on Covers for all 64 residual roster entries. It is not an unconditional upper bound.

## Canonical62 structural preflight

- Preflight [45775970314](https://github.com/FlareZ123/bb6/actions/runs/45775970314) passed.
- Strict link: 8,082 reachable modules across Canonical64, Raw112Base and Raw58; duplicate kernel declarations/import descriptors agree exactly.
- Raw112 and Raw58 parents are each uniquely present in Canonical64, distinct, and root-compatible. Removing both simultaneously gives a verified 62-entry roster.
- The integrated quotient/soundness interface compiles with only the explicit Raw112 parent-cover axiom stub plus standard Lean axioms.
- **This is not a real Raw112 Cover proof and does not establish a 62-machine upper bound.** See `im-results/agent4-raw58/`.

## Raw112 recovery

- Run [45751911115](https://github.com/FlareZ123/bb6/actions/runs/45751911115) attempt 2 failed shards 1,4,5. Shards 0,2,3,6,7 have successful artifacts.
- Shards 4 and 5 were confirmed runner shutdown / exit 143 without Lean theorem diagnostics. Shard 1's log inspection was blocked by GitHub API rate limiting.
- Missing groups:
  - 1: Raw112Branch01, Raw112Branch09, Raw112Branch17
  - 4: Raw112Branch04, Raw112Branch12, Raw112Branch20
  - 5: Raw112Branch05, Raw112Branch13, Raw112Branch21
- I added `assemble-existing` mode to `.github/workflows/agent47-raw112-parent-cover.yml` (commits `5e1473d8d044ecb263f0d015d6a9d78c46634713`, `ce68d013395970218fe064aec0b8b015a644f175`). Once all eight shard artifacts exist in a source run, dispatch with `mode=assemble-existing` and `source_run_id=<run>`. It reuses the existing artifacts and retains strict source/import/object/compiler/provenance hash checks; output artifact name is the standard `raw112-closed-parent-cover`.
- A third failed-job retry was blocked by the GitHub Actions API rate limit, which returned retry-after 17m16s around 07:35Z. Retry after the rate limit clears. Prefer a targeted lower-memory `--jobs 1` retry for the three missing groups; if the new artifacts are from another run, extend assembly to combine selected artifacts across run IDs rather than recomputing the five successful groups.

## Other candidates

- Raw118 parent assembly run 45768921666 remains in progress.
- Raw57 and Raw118 membership helpers are not parent-cover proofs. If both parent Covers become source-accepted, consider adding both directly to one Canonical64 parent list rather than chaining unaccepted frontiers.

No exact BB(6) value has been established. The immediate critical path is a genuine Raw112 parent Cover, followed by the real Canonical62 source/axiom gate.
