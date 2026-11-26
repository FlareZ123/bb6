# Raw39: six accepted child bounds, five remaining canonical obligations

**Status:** locally kernel-checked, artifact-linked conditional parent Cover; not a complete Raw39 Cover or a BB(6) upper bound. The first-hole query is A1 at live time 6 for `1RB---_1RC---_0RD---_1LD0RA_------_------`.

`Raw39AcceptedSix.lean` proves `BB6.Agent11Raw39AcceptedSix.parent_cover_five`: at any B ≥ 2354, bounds for the five remaining canonical child refinements 0LE, 1LA, 1LB, 1LE, 1RE imply a literal parent `Cover (WeightedBound B) p39`. The original normalized first-hole join checks the weighted halt case, nine cycle branches, the six accepted semantic bounds below, and handles unused E/F state symmetry. No assumption is made about the five remaining branches.

| A1 move | Weighted bound | Source run | Artifact |
| --- | ---: | ---: | ---: |
| 1RB | 175 | 45639153728 | 15036330602 |
| 0RB | 1271 | 45644271619 | 15039311430 |
| 1RC | 1882 | 45644280485 | 15039350734 |
| 0RE | 944 | 45680199670 | 15054707946 |
| 0RC | 2354 | 45753648611 | 15087393537 |
| 0LA | 1003 | 45766252232 | 15091944603 |

All six exact archives were linked locally after checking the per-module source/object SHA256 hashes in each embedded manifest and equality of all shared module pairs. Their 88+100+102+97+94+232 manifest entries yield 456 distinct source/object pairs. The first four source revisions are 439ff1526b1d9b19b3e5a02f8c1c764eadcbdbda, c39dbcb430765b7d8f630dc7fd7633e613bee8e6 (twice), and 9e3bfe908a91b42031d33e46c42b03c71b1a84b1; the last two are aa832e9f7734b28505baa8527de0f19979f009ca and a82f9d0ca7b85b6dfb2b32e09d6d36c1e8133680. The last two archive digests are 2c085341ac516ae6b8e40796c96e77d77aa974fc97a79ffef508f5f57925d7d1 and d0a7a4bc52c65f54fe386efc077ac56635becbf0af02d69dd7c57dc97da64942. This is a specifically audited legacy object link, not a claim of identical whole source revisions.

Lean 4.36.0-rc2 compiled the exact new source in 9 seconds (peak RSS 2029144 KiB). `remaining_count` depends only on propext; `parent_bound_five` and `parent_cover_five` depend only on propext, Classical.choice and Quot.sound. Source SHA256: 9818e7a13b85f1dd5ce0890807e0bd329fafce6c5135180fa507db98b6e77495. Object SHA256: 77bc535e072a6c5dab4194e10c166276336976fae4bd3c74969585abf691bd42.

Reproduce by downloading those exact artifacts, checking manifests and shared bytes, and placing the source in the merged directory. Set LEAN_PATH to the directory and compile with the same Lean release. A full fresh source rebuild is distinct from this artifact-linked check.

The older `Raw39StableCut.lean`, `Raw39StableIntegrated.lean` and `Raw39SymmetryCut.lean` prove eleven literal residuals, the E/F transport and seven canonical residuals; the new theorem supersedes their conditional parent interface without replaying large audits. The older joint audit 45719963229 was cancelled without an artifact. The 1LB candidate partition is described in [Raw39LBClosure.md](Raw39LBClosure.md). The [0LA candidate dossier](Raw39LAFrontier.md) now has the accepted source run above. 1LA and 1RE candidate discovery is complete, but the source checks are pending. The remaining difficult discovery branches are 0LE and 1LE. Do not claim a global roster reduction before all five conditions are discharged.
