# Raw39 A1=1LA: complete candidate frontier

Literal child `1RB1LA_1RC---_0RD---_1LD0RA_------_------`. Normalized tree: 125476 translated cycles, 34070 last holes, 7159 splits, 5088 open. Full 24-way enumeration projected byte-identically to the normalized tree. Candidate weighted bound 349.

All 5088 open indices covered once: FAR4943, asym70, rungram69, blockgram273, runblock410, affine421/457/460/503. No unclassified discovery leaves.

410's initial run-block closure had 36374 rows and 1541/314 stack states; context/transition partition refinement reduced to 1691 rows and 217/124 stack states, 409 edges. Reduced closure was recomputed. Lean's original FastBiDFA checker checks the graph independently of the minimizer.

Pinned data `1LA-frontier.json.xz.b64` (uncompressed JSON SHA256 5e962e1281c8be71b1e34dd7e6c452f5fbc50449f2b464fe82c1d0b864b84b9b). `prepare_raw39_semantic_children.py 1LA` emits candidate theorem `BB6.Agent11Raw391LA.all1LA`. Full generator and Lean source acceptance still pending. Do not claim a new Cover.
