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
