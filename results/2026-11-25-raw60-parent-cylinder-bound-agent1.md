# Raw60 six-hole parent: complete weighted bound 1175

The literal partial machine `1RB---_1RC---_0RD---_1LD1RE_---1RA_------` admits a universal weighted halting bound of **1175** over every compatible completion. This discharges an entire six-hole cylinder, including its possible incoming blank-write delay and final halt query, at any target score at least 1175. It is a local parent theorem, not a global maximality certificate.

## Certified statement and construction

[Raw60RootFull.lean](../im-results/agent1-raw60/Raw60RootFull.lean) exports `BB6.Agent1Raw60Root.all60 : ∀ m, compatible parent m → WeightedBound 1175 m`.

The first unassigned slot A1 is reached after seven ordinary moves. Its halt option and eleven immediate side cycles are covered directly; all thirteen other ordinary options have exhaustive weighted child certificates. The child bounds in the order 0RC, 0RE, 0LD, 0RF, 0LB, 1LA, 1LB, 1LC, 1RF, 0LC, 0LF, 1LF, 1RE are respectively 376, 719, 176, 1175, 258, 178, 620, 253, 276, 251, 802, 1175, 211. The maximum is 1175. The certified tree uses finite query and cycle witnesses, FAR and two-sided stack invariants, symbolic pumps, and recursively quantified nonhalting proofs; the discovery programs are outside the proof kernel.

Original-source Lean 4.36.0-rc2 acceptance: [run 45686044022](https://github.com/FlareZ123/bb6/actions/runs/45686044022), source revision `9dfc3b3b5b0247e01dad1a8c323fd2a4f6963589`, successful child job 139458804753 and strict parent job 139473223503. The parent job consumed all thirteen accepted child artifacts and audited the named theorem. Artifact `raw60-parent-proof` ID 15057164854, SHA256 `0d4d87e1d342d3771666a292cef60051a5aad7fbd52a26215f4859b924282c5d`. [Reproduction dossier](../im-results/agent1-raw60/README.md).

## Stable global contract

[Raw60StableContract.lean](../im-results/agent1-raw60/Raw60StableContract.lean) locally compiles against the pinned canonical core (artifact 14997966221) with only propext, Classical.choice and Quot.sound. It proves exact table membership in the stable canonical76 roster and proves the filtered complement has length 75. Its generic local-partition and selected-parent Cover consumers keep all unmatched parents and all unresolved children explicit.

The [direct consumer](../im-results/agent1-raw60/Raw60StableAccepted.lean) also compiled locally using the independently accepted canonical76 and Raw60 artifacts, with only standard axioms. It instantiates the actual Raw60 proof and reduces exactness at any B ≥ 7014 to the 75 other Covers and an attaining witness. This uses the experimental legacy kernel-data equality link for five same-source, non-byte-identical shared modules; it is a local artifact-backed proof, not a fresh strict shared-core source-CI acceptance. Do not count it as the accepted global 75-way cut or add it to other alternative roster counts until the shared integration policy accepts the dependency union.
