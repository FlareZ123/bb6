# Raw139 C/1 sibling coverage

These are disjoint four-hole children of the champion-compatible raw139 path at depth four. They do not include the champion's C/1=0RF branch. Each listed candidate retains every ordinary first-hole completion; weighted bounds include the blank-delay and halt charge of at most six.

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
| 1RB | 2163 | 91 | 317 | All 91 block proofs and eight of nine branch modules locally accepted; last branch and root pending |

The 1RB parent is `[7,24,11,24,14,7,3,16,12,11,24,24]`. Its 94 first-hole splits give 2163 ordinary leaves: 1177 translated cycles (one late), 530 last-hole cases, 365 ordinary FAR and 91 block-FAR. Maximum first-hole query 311; weighted candidate bound 317. The two previously open block cases 60 and 66 both admit width-two, run-one, modulus-five left automata, with 8/24 and 6/23 left/right states. No reflection or width-four encoding is required. All block proof axioms are standard; local original-source artifact-backed preflight uses the ZeroLD closure and BlockMacro/BlockFAR/BlockFARBridge from accepted raw110 word artifact 15013294241, plus exact BlockMacro2 and BlockFAR2 source (Git blobs 3d0a85da and 0e281058). Root acceptance is pending, not a claimed global reduction.

Reproduce `1RB` via `bash im-results/agent48-raw139-f1-oneRA/reproduce-blocks.sh c1 OneRB`; the existing manual sibling workflow accepts `kind=c1,sibling=OneRB,source_sha=<pinned commit>`. The same generator covers the other candidate specs. The 1RB spec uses cutoff 350, the older 1LA/0LB/1LB/0RC/0RB specs cutoff 600. All FAR searches use depth 2 initially, with stored extra DFAs and exact late cases where needed. All generated proofs are untrusted inputs to the kernel checker. Late cycle entries do not affect the halt bound.

Do not treat a candidate partition as a certified Cover; no global roster reduction follows before the exact table consumer is compiled.
