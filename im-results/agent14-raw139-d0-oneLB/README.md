# Raw139 D0=1LB: exhaustive candidate

Exact parent: `[7,24,11,24,14,24,6,16,12,11,24,24]`. Target theorem: `BB6.Agent14Raw139D0LB.all_completions_weighted`, weighted bound 7252.

**Status:** full candidate certificate generated; original-kernel compilation underway at checkpoint. Do not count as accepted until the root theorem compiles.

The first-hole tree has 1124 ordinary 24-child splits and 25853 terminal leaves: 17938 initial side cycles, 5966 initial last holes, 1701 FAR, 242 block FAR, 3 late side cycles, and 3 late last holes. No remaining computational holdouts. The longest last-hole query is 7246 steps on [7,24,11,22,14,23,6,16,12,11,3,17] at A1. Its separate 512-step segmented zipper proof has already compiled against original dependencies, exporting `BB6.Agent14Raw139D0LBLong.checked`. The ordinary exact-query bound follows from the compatible default machine and zipper embedding; last-hole soundness then handles every completion.

The full generator has 31 block shards, 62 finite-audit shards, 17 composition shards, one segmented trace module, and one root module. It uses the common D0=0LF generator and the original Agent 48 automata routines, with sparse direct import dependencies. Reproduction: `bash im-results/agent14-raw139-d0-oneLB/reproduce.sh` using Lean 4.36.0-rc2. Local dependency artifact 15057921816 from original-source C1 audit 45689490709.

Archive SHA256 d560c6e2b27fa8f0f41b38070d7446a0f9c8053c35a8501b4d7ad6844b3aa5a3; root SHA256 87f0a8be0bca98a4f9c329722488e7e18ead267b3460dd1631471b46031e7809. The generator asserts the exact candidate leaf partition and Lean checks all witnesses. No full BB(6) upper bound asserted.
