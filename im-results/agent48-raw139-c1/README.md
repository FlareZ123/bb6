# Raw139 C/1 sibling coverage

These are disjoint four-hole children of the champion-compatible raw139 path at depth four. They do not include the champion's C/1=0RF branch. Each listed candidate retains every ordinary first-hole completion; weighted bounds include the blank-delay and halt charge of at most six.

## Current scope: twelve-sibling stable contract

The new `Raw139C1Batch.lean` composes the ten generated and two direct exact parent tables at common weighted bound **2511**, with a reusable `consume` theorem that retains every unmatched frontier entry. Seven other nonchampion C/1 siblings have established cycle witnesses in `ChampionResidualFrontier.lean`; the remaining four C/1 siblings (0LA, 0RA, 0LC, 1LC) are separate proof programmes. The champion C/1=0RF continuation is not part of this batch. The batch composition passes local Lean 4.36.0-rc2 elaboration against a type-matched model, but full original-source acceptance is **pending**. No complete parent or global roster closure is claimed.

The accepted OneRB and OneLF producer artifacts are reused by `reproduce-batch.sh`, with the existing closure compiler checking exact source, object and transitive dependency identities before reuse; mismatches cause recompilation. The existing manual sibling workflow now has a `kind=c1batch` target. It compiles the single batch root and rejects unapproved axiom profiles for all four exports. No new workflow is introduced.

## Source-backed direct covers

C/1=1RC (code 11) and C/1=1RE (code 19), exact tables `[7,24,11,24,14,11,3,16,12,11,24,24]` and `[7,24,11,24,14,19,3,16,12,11,24,24]`, have direct two-state FAR witnesses. Both cover all 25^4=390625 completions at weighted bound 0. Original Lean 4.36.0-rc2 dependencies came from accepted ZeroLD artifact 15020208929; both theorems use only propext, Classical.choice and Quot.sound. Module `Raw139C1Direct.lean`, namespace `BB6.Agent48Raw139C1.OneRC` and `.OneRE`, theorem `all_completions_weighted`. Exact grafts are separate.

## Complete candidate partitions

| C/1 | Ordinary terminal leaves | Block FAR | Proposed bound | Proof status |
| --- | ---: | ---: | ---: | --- |
| 1LA | 2508 | 56 | 533 | Candidate |
| 0LB | 2094 | 43 | 542 | Candidate |
| 1LB | 2117 | 56 | 712 | Candidate |
| 0RC | 1473 | 63 | 1853 | Candidate |
| 0RB | 1772 | 88 | 2511 | Candidate |
| 1RB | 2163 | 91 | 317 | Source-accepted in run 45689490709; artifact 15057921816 |

| 1RA | 2209 | 276 | 725 | Complete computational candidate |
| 0LF | 3957 | 120 | 683 | Complete computational candidate |
| 1LF | 3819 | 132 | 232 | Source-accepted run 45726436580; artifact 15075350238 |
| 1RF | 4739 | 601 | 2242 | Complete computational candidate |

The four new complete candidates (1RA, 0LF, 1LF, 1RF) were obtained by the same first-hole scan, with late cycles/last queries and width-two/three block-FAR saturation. In total they contain 14724 terminal ordinary leaves. The larger 1RA case 77 needs the width-two phase-aware run-four modulus-seven abstraction (47 left states, 120 right nodes). All eight final 1RF holdouts were resolved by extending the width-two/three run/modulus search; none uses reflection. The 1LF spec has since passed the existing exact-source audit in [run 45726436580](https://github.com/FlareZ123/bb6/actions/runs/45726436580), artifact 15075350238. The other three still require original-source replay.

The 1RB parent is `[7,24,11,24,14,7,3,16,12,11,24,24]`. Its 94 first-hole splits give 2163 ordinary leaves: 1177 translated cycles (one late), 530 last-hole cases, 365 ordinary FAR and 91 block-FAR. Maximum first-hole query 311; weighted candidate bound 317. The two previously open block cases 60 and 66 both admit width-two, run-one, modulus-five left automata, with 8/24 and 6/23 left/right states. No reflection or width-four encoding is required. All block proof axioms are standard; local original-source artifact-backed preflight uses the ZeroLD closure and BlockMacro/BlockFAR/BlockFARBridge from accepted raw110 word artifact 15013294241, plus exact BlockMacro2 and BlockFAR2 source (Git blobs 3d0a85da and 0e281058). All 12 block shards, nine branch modules and the root compiled locally. The last branch succeeded when run in isolation after a concurrent shell timeout. Exported theorem `BB6.Agent48Raw139C1OneRB.all_completions_weighted` in `Raw139C1OneRBCover.lean` has axiom profile `[propext, Classical.choice, Quot.sound]`, as does `hRoot`. The full pinned-source Lean 4.36.0-rc2 audit succeeded in run 45689490709 (job 139470850210, source commit 04fec001d605129ad4b8fda81937041205cd508c): 74 project modules compiled from the exact root, and `BB6.Agent48Raw139C1OneRB.all_completions_weighted` has only `[propext, Classical.choice, Quot.sound]`. Artifact 15057921816 contains the manifest, imported sources, and `.olean` closure. This supersedes the earlier pending-audit status. The exact raw139 parent-to-list graft remains pending; no whole raw139 closure is implied.

Reproduce `1RB` via `bash im-results/agent48-raw139-f1-oneRA/reproduce-blocks.sh c1 OneRB`; the existing manual sibling workflow accepts `kind=c1,sibling=OneRB,source_sha=<pinned commit>`. The same generator covers the other candidate specs. The 1RB spec uses cutoff 350, the older 1LA/0LB/1LB/0RC/0RB specs cutoff 600. All FAR searches use depth 2 initially, with stored extra DFAs and exact late cases where needed. All generated proofs are untrusted inputs to the kernel checker. Late cycle entries do not affect the halt bound.

Do not treat a candidate partition as a certified Cover; no global roster reduction follows before the exact table consumer is compiled.
