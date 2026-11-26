# Raw13 accepted-parent integration

[Agent46Raw13AcceptedParentGraft.lean](Agent46Raw13AcceptedParentGraft.lean) gives the exact 1697-entry retained complement of the accepted 1708-entry phase cut after consuming eleven distinct independently source-audited six-hole parents. Every completion of each parent has weighted bound 7014; the quotient-aware soundness theorem retains the base bound 21269 for eliminated cases. It filters by `tableOK` and uses `tableOK_sound` and `safe_quotient`.

| Parent(s) | Successful source run | Artifact | ZIP SHA256 |
|---|---:|---:|---|
| Base 1708 | 45669304183 | 15052276180 | fecd16e749382d341796503f388b02349e176904de5f193935f702cfc4a756d6 |
| 484 | 45752971312 | 15087066527 | a6b559b37bf265b160e9837595da458854244e07f94ca755f0050f069c6adbaf |
| 540 | 45752966270 | 15087265608 | 739a34c5cb3c5f37627e1f68440b6d43402cf45154a81f46ebee173a61929e37 |
| 1420 | 45778821164 | 15099125782 | 18a5710c1b860c4ca6d2bdadcdedb07eb99ad19b239036069d0dfbcbf4bef3d4 |
| 830, 1422 | 45779309909 | 15099506359 | 24287f0c20d5940ac919fd59b586f8eb612588384d997508d3e96885e5bc76e5 |
| 503, 1046 | 45849588820 | 15135720074 | d1a04550690b029e3e9d13ba881bbcd25a13b31fff60793fa86867bd66459c19 |
| 231, 323 | 45851179262 | 15135299891 | 05962ad23b74929ec1f9d27b8767ac42f1a781c5fece1564dc5acba383522ddc |
| 321, 482 | 45852032702 | 15136488902 | ed468494d8d7342bca98eb892cc6a19bb10f91e4150fee11ae5cbdca36baaf1b |

The artifact module inventories establish the actual batch targets (323 already accepted with 231; 1100 not in the 321/482 artifact). All eight ZIP SHA256 values matched metadata. The recursive project imports from twelve roots yield 881 unique modules. Exactly five distinct binary duplicate pairs occur (SparseZipper, FrontierMass, TwoFirst, CrossCoverage and BB6Coverage); each passed the existing CompareKernelImports.lean check for exact kernel declarations and import descriptors. Lean 4.36.0-rc2 compiled the integrated source with `-j1` in 28.84 seconds, peak RSS 2925428 KiB. Both `refined_sound` and `refined_count` report only `propext, Classical.choice, Quot.sound`.

This is a **local artifact-backed integration** of source-accepted parent bounds, not a new full original-source CI run or Canonical64 roster reduction. It does not consume 682 (previously locally checked but no retained source artifact), 1100 (candidate), or the two independently accepted five-hole fresh-state parents 0LE/1LE. The 1697 retained obligations, including the hard #754 cylinder, remain to be covered. No exact BB(6) upper bound follows.

The earlier [five-parent result](FiveParentGraft.md) and [six-parent source](Agent46Raw13SixParentGraft.lean) are historical narrower integrations.


## Post-graft branchBatch inventory (2026-11-26)

Two later successful runs of the same `branchBatch` workflow exist and must be reconciled before any further Raw13 branch dispatch:

| Run | Source SHA | Artifact | Artifact size | Catalog at source SHA |
|---|---|---:|---:|---|
| 45873240434 | `5d7531c100904c09bef67473fbed930d04a46a8f` | 15145207648 | 80,427,686 bytes | 10 keys: 231, 321, 323, 482, 503, 682, 830, 1046, 1100, 1422 |
| 45873898225 | `637c0535dd58b701433aef4bca3cf5f05df1db56` | 15144394253 | 101,409,956 bytes | the preceding 10 plus 600571, 600573, 601395, 601396, 601452, 601541 |

At run 45873240434's source snapshot, the only catalog IDs not already represented in the eight source-audited artifact rows above were 682 and 1100. This makes it plausible that the successful run source-audited those two, but the GitHub Actions run metadata does not expose the `workflow_dispatch` branch input. Do **not** mark either accepted until the artifact's generated `Agent46Raw13BranchBatch.lean` import list (or an equivalent manifest) is inspected.

At run 45873898225's source snapshot, six fresh IDs had just been added. The workflow accepts at most four IDs per batch, so this run can cover no more than four of those six; its exact subset is unknown. Five further IDs (600489, 600542, 601454, 601456, 601558) were added only in a later catalog revision and were not available to either run above. The current catalog has 21 keys in total.

This invocation dispatched run 45889186819 for `682 1100` before discovering the two earlier successful runs. It was cancelled at 2026-11-26 20:32:08Z and produced no artifact. This cancellation avoids a likely duplicate; do not repeat that batch. The 11-parent integration and 1697 count above remain the only integrated result until the later artifact inventories are reconciled. The exact branch modules should be checked before updating the graft.

The local Python/container shell returned `ClientError` on repeated attempts in this invocation, so the ZIP contents could not be inspected locally. Next step: inspect artifacts 15145207648 and 15144394253 when a shell is available, or add an explicit branch manifest to a future run; do not spend another CI run merely to rediscover their inputs.
