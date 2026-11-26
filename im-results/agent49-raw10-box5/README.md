# Raw10 Box 5 complete candidate search and differential stack certificates

## Scope and status

Original base34 index 5 fixes codes [8,14,11,7,17,4,9] in slots A0 through D0; D1 excludes code 2, and E0/E1/F0/F1 are unrestricted. This rectangle contains 9,375,000 total completions. Codes 0 and -1 mean assigned halt and unknown respectively. The source-index equality and full rectangle theorem are NOT yet checked.

A first-hole DFS produced 5,700 branch nodes, 5,700 halt leaves (maximum ordinary score 155), 19,047 translated-cycle leaves, 109,528 all-ordinary total tables, and 518 capped sparse leaves. Sparse n-gram saturation finds 505 of those 518 nonhalting candidates at width <=23; RLE stack relations cover twelve more. The final row (zero-based open ID 483) is [8,14,11,7,17,4,9,22,-1,23,16,5]. Its only hole is E0.

**New abstraction:** store the leading stack bit and a run-length abstraction of the consecutive-bit XOR stream. Pushing bit b changes the leading bit to b and pushes b XOR oldHead into the run-length summary. The ordinary RLE of a long alternating stack has many runs; differential RLE compresses that into one run. Parameters (2,2,4) on both stacks yield 271 reachable abstract configurations for row 483.

All 13 emitted two-sided stack automata certificates (12 ordinary RLE and one differential RLE) compiled locally in Lean 4.36.0-rc2 against the byte-exact original TwoSidedAutomata.lean (Git blob c04bf81e19d55b3d028c714e628246a4b917f03c) and source/oleans from accepted artifact 15054146521. Each exported never theorem has only propext, Classical.choice, Quot.sound. The 505 n-gram certificates and the entire first-hole partition remain to be assembled and checked. Thus weighted bound 160 is a **candidate**, not yet a source-proved rectangle bound or a canonical roster reduction.

## Reproduce

Extract source.tar.xz (SHA256 0837d8a34fda69c6699e1e9b7107e489645abc98d90447b61bfef980a7d412d5), run bash replay.sh. This builds the C++ discovery search, regenerates open.csv and ngram.txt, finds RLE/differential parameters, and emits Box5Automata.lean. For Lean, use the repository's TwoSidedAutomata checker and dependencies. The generators are untrusted; only the kernel checks establish nonhalting. Reuse AsymNGram sparse tries for the other 505 and compress last-hole branches with the existing last-hole theorem. No new workflow was created.

