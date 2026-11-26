# Raw39: exact eleven-cylinder semantic residual cut

**Status:** locally kernel-checked original-source artifact-linked parent refinement; not a complete Raw39 Cover or a BB(6) upper bound. The first-hole query is A1 at live time 6 for `1RB---_1RC---_0RD---_1LD0RA_------_------`.

The theorem `BB6.Agent11Raw39Stable.cut_integrated` proves every total completion of this exact parent satisfies `WeightedBound 1882` or extends one of eleven explicit A1 refinements: 0LA, 0LE, 0LF, 0RC, 0RF, 1LA, 1LB, 1LE, 1LF, 1RE, 1RF. The halt case uses the weighted first-hole theorem and nine ordinary branches use source `zipCycle_sound`. The four remaining closed ordinary branches use the independently checked semantic bounds below. This replaces the expensive attempted joint audit-tree replay with a small proof using the actual exported child statements; no new enumeration or workflow is needed.

| A1 move | Weighted bound | Source run | Artifact |
| --- | ---: | ---: | ---: |
| 1RB | 175 | 45639153728 | 15036330602 |
| 0RB | 1271 | 45644271619 | 15039311430 |
| 1RC | 1882 | 45644280485 | 15039350734 |
| 0RE | 944 | 45680199670 | 15054707946 |

The four archives were downloaded from those exact artifact IDs; SHA256s match GitHub metadata, and every source/object hash in each embedded manifest was checked (88+100+102+97 entries). The union contains 465 paths, with only the four independent manifest.json files differing; all overlapping Lean sources and objects are byte-identical. These artifacts have different source revision labels (439ff1526b1d9b19b3e5a02f8c1c764eadcbdbda, c39dbcb430765b7d8f630dc7fd7633e613bee8e6, 9e3bfe908a91b42031d33e46c42b03c71b1a84b1), so this is a specifically audited byte-identical legacy object link, not an assertion that whole source revisions match.

On local Lean 4.36.0-rc2, the exact `Raw39StableCut.lean` and `Raw39StableIntegrated.lean` compiled in 1.17s/1.83s respectively; peak RSS 1.65/1.98 GB. The exported `cut_integrated` and generic `cut_sound` depend only on propext, Classical.choice and Quot.sound; residual_count on propext; residual_mem on propext and Quot.sound. No sorryAx or native_decide. SHA256 of the two exact source files respectively: 4d74f8e3b281e63271616c4a4c1d4f81d3be27ea203752fda47abf0346780e44 and 69a5d129d2125317d96f48125310cf29b707055eedcf762acaaed240d6843dbd.

To reproduce, download the four artifact ZIPs, extract into a common directory after checking shared source and object bytes, preserving separate manifests. Place these two modules there and run Lean with LEAN_PATH set to that directory, first compiling Raw39StableCut.lean to Raw39StableCut.olean, then checking Raw39StableIntegrated.lean. A full fresh source rebuild is distinct from this local artifact-linked check.

The older Raw39CombinedPartial/Canonical86 joint audit run 45719963229 was cancelled after two hours with no output artifact. The 0RC candidate at bound 2354 is unaccepted (run 45720481054 cancelled). Neither is used in the theorem above. The useful next step is the actual missing A1 child Covers, especially completing 0RC, and eventually instantiating a stable Raw39 parent Cover at the champion score. Do not claim a global 86-way roster or a whole Raw39 bound from this local eleven-residual cut.
