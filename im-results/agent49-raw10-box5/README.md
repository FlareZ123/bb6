# Raw10 Box5 source-accepted exhaustive Cover

## Scope and status

Original base34 index 5 fixes codes [8,14,11,7,17,4,9] in slots A0 through D0; D1 excludes code 2, and E0/E1/F0/F1 are unrestricted. This rectangle contains 9,375,000 total completions. Codes 0 and -1 mean assigned halt and unknown respectively. The exact source-index equality and full rectangle theorem are now accepted in original-source Lean CI; see run 45892933847 below.

A first-hole DFS produced 5,700 branch nodes, 5,700 halt leaves (maximum ordinary score 155), 19,047 translated-cycle leaves, 109,528 all-ordinary total tables, and 518 capped sparse leaves. Sparse n-gram saturation finds 505 of those 518 nonhalting candidates at width <=23; RLE stack relations cover twelve more. The final row (zero-based open ID 483) is [8,14,11,7,17,4,9,22,-1,23,16,5]. Its only hole is E0.

**New abstraction:** store the leading stack bit and a run-length abstraction of the consecutive-bit XOR stream. Pushing bit b changes the leading bit to b and pushes b XOR oldHead into the run-length summary. The ordinary RLE of a long alternating stack has many runs; differential RLE compresses that into one run. Parameters (2,2,4) on both stacks yield 271 reachable abstract configurations for row 483.

All 13 emitted two-sided stack automata certificates (12 ordinary RLE and one differential RLE) compiled locally in Lean 4.36.0-rc2 against the byte-exact original TwoSidedAutomata.lean (Git blob c04bf81e19d55b3d028c714e628246a4b917f03c) and source/oleans from accepted artifact 15054146521. Each exported never theorem has only propext, Classical.choice, Quot.sound. The later complete proof-source archive assembles the 505 sparse n-gram certificates, 13 two-sided automata certificates, and the full first-hole partition. Original-source Lean CI now accepts the exact rectangle bound 160; this remains a local Raw10 Cover, not a canonical roster reduction.

## Reproduce

Extract source.tar.xz (SHA256 0837d8a34fda69c6699e1e9b7107e489645abc98d90447b61bfef980a7d412d5), run bash replay.sh. This builds the C++ discovery search, regenerates open.csv and ngram.txt, finds RLE/differential parameters, and emits Box5Automata.lean. For Lean, use the repository's TwoSidedAutomata checker and dependencies. The generators are untrusted; only the kernel checks establish nonhalting. Reuse AsymNGram sparse tries for the other 505 and compress last-hole branches with the existing last-hole theorem. No new workflow was created.



## 2026-11-26: full proof-source acceptance

The original discovery partition was compressed using a sound last-hole rule. When every row except the current hole is assigned an ordinary transition, a halt there is checked by the finite-prefix checker; every ordinary choice gives a total table with no halt instruction. Thus 4,633 split nodes and their 24 ordinary children each become a single last-hole certificate. The resulting preorder tree has 26,332 nodes: 1,067 split, 1,067 explicit halt, 19,047 translated cycle, 4,633 last-hole, 518 invariant leaves. The maximum finite score stays 155, yielding the now source-accepted weighted bound 160. All 518 open rows are exactly matched to 505 emitted sparse n-gram tries and 13 two-sided automata certificates. The new generator pins the known automata parameters rather than rerunning their discovery search.

Extract the existing source.tar.xz and the new proof-source.tar.xz (SHA256 0894fce4eb33d1d2f8c2de7641d46639ed06e715fc719bbaab9a58202f2f5811) in one empty directory and execute bash replay-proof.sh. The local C++/Python regeneration succeeded, creating 25 Lean shards (second-level kernel checks for each nontrivial shard), Box5Core, Box5Hard, Box5Automata and Box5SourceConsumer. The latter is designed to export source_index5, sourceBound (160), and residual_without_box5. Each split's children are checked against the actual allowed domain rather than trusting the discovery tree, and each certificate is applied to the accumulated partial table. The source index is checked extensionally against raw10Remainder[5]!, not merely matched by count. The full generated source closure is now accepted; details and the exact conditional parent interface are recorded below.

The existing agent13-coverage.yml dispatch target weighted-tnf-raw10-box5 regenerates and compiles the entire source closure, with rejection of sorryAx/native_decide. No standalone workflow.


## Original-source acceptance and parent integration

- **Successful run:** [45892933847](https://github.com/FlareZ123/bb6/actions/runs/45892933847), source revision `3e22006dbd310f543d86d7a0cf164682518c83e7`, Lean 4.36.0-rc2.
- The full closure compiled **127 project modules** from `Raw10RefinedBox7.lean`.
- `BB6.Agent49Box5.source_index5`, `sourceBound`, and `residual_without_box5` passed. The source-bound theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
- The same closure rebuilt and source-accepted Box7: `BB6.Agent49Box7.raw10_box7_closed` and `residual_without_box7`, with the same standard axiom profile and weighted bound 41.
- The exact combined adapter declarations `open31`, `open29`, `parentCover31`, and `parentCover29` also compiled with only the standard axiom profile. The counts are kernel-checked; the parent Covers remain conditional on the explicit unresolved-box bounds and held-leaf premise.
- The workflow rejects `sorryAx` and `native_decide`; the successful run passed that gate.

The source-accepted closure is now preserved as GitHub artifact `raw10-box5-box7-source-closure` from [run 45896143748](https://github.com/FlareZ123/bb6/actions/runs/45896143748), artifact ID `15154018415`, SHA-256 digest `5f6a27b9fb68627e077a6168fe82609eea07cccba437559da6e6df7454ef383d`, size 121,164,690 bytes, retained through 2026-12-26. It contains the source/import/olean manifest, compiled dependency closure, source archives, and pinned generator/audit inputs. The Box6 consumer now downloads this artifact as its precompiled base and compares its shared modules against the independently built Box6 closure.
