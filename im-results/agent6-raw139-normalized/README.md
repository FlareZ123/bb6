# Raw139 normalized spine: conditional 67-table reduction

**Status:** Kernel-checked local Lean proof against the accepted Canonical77 dependency artifact. The theorem is conditional on 43 sibling covers, two continuation implications, the terminal champion-cylinder cover, and the remaining 67 table covers. It is not a global upper bound.

[Raw139Normalized.lean](Raw139Normalized.lean) defines the exact raw139 root and seven first-hole refinements, checks their query times (3, 4, 7, 8, 11, 12, 53), and applies the established weighted TNF branching theorem at each split. The root has only four introduced states; the first split therefore needs destinations A–E, and the four F-destination siblings are represented by their E counterparts. This is a semantic weighted-bound argument using the original normalization theorem, not a cardinality-only deletion.

The 47 certified nonhalting witnesses include the 38 in the older ChampionResidualFrontier and the nine already proven separately in EarlySiblingCover (run 45556284591): E0=0LE,1LE and D0=0LC,1LC,0LD,0RD,1LD,0LE,1LE. Their original checker is applied again here by kernel reduction. The 43 acceptedRows are the exact address list from the current Agent14/Agent6 sibling consumers (8 D0, 12 C1, 12 F1, 11 F0). The two F0 partial covers use the remaining one-hole refinements F0=0RC/A1=0RD and F0=1RE/B1=0RD.

The kernel-verified count of the remaining list is 67, with per-depth counts [19,22,18,0,4,2,2]. Relative to the proposed 80-row list this removes nine previously proven cycles and four state-label duplicates; it does not remove the raw139 parent from the global roster. In particular D0 has no residual sibling when its eight independent covers are supplied.

## Reproduction

Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a); Canonical77 dependency artifact 14997966221, run 45554648116, downloaded ZIP SHA256 b55e4c939da70aaa4d2f50f5721b9183ab776682f1b682f647ee27aa6cc5da17. Extract the artifact, set LEAN_PATH to its extracted module directory, and run Lean on the source file. Local output:

    'BB6.Agent6Raw139Normalized.raw139_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
    'BB6.Agent6Raw139Normalized.count' depends on axioms: [propext, Classical.choice, Quot.sound]
    'BB6.Agent6Raw139Normalized.depthCounts' depends on axioms: [propext, Classical.choice, Quot.sound]

The committed source blob 88e520f0d7f371031e1e4325d03015e323e46a73 exactly matches the locally checked file. The imported .olean modules came from the accepted artifact; this is not a fresh source rebuild of the transitive dependencies.

## Next mathematical step

Supply the existing sibling covers and continuation implications to raw139_cover, or consume the same normalized structure in the existing Agent14 integration. Prioritize the 67 retained cylinders, especially the still-large D1/E1/E0 families, rather than repeating the old 80-row consumer or the already discharged D0 siblings. The terminal p7 cover still requires the exact champion machinery. No claim of BB(6) exactness follows yet.
