# D0=9 normalized certificate pipeline

2026-11-28, Agent 6. Decode with `cat source.b64.0* | base64 -d > pipeline-source.tar.xz; tar -xJf pipeline-source.tar.xz`. SHA256 of compressed bytes: `784b65cdbadd8979a40a43dd78b0aa768ce3fece0ea9b66dd8d9362ba43bc4e3`. See extracted BUILD.md for dependencies and commands.

Target `[7,24,11,24,14,24,9,13,24,24,24,24]` (D1=0RD,D0=0RC). Exhaustive normalized candidate tree has 1,115,867 terminal branches (14 immediate cycles plus six C1 subtrees). The six C1 codes 2,6,16,17,18,19 have respectively 126707,118454,157160,121579,368461,223492 terminal branches. Strong classification yielded 1688 n-gram, 2134 block-FAR, and 41 prior late certificates across 3863 strong leaves. These counts and generated candidate trees are untrusted discovery; only checked Lean theorems constitute proof.

New D1PackedTree.cover, D1QuickTree and D1TreeTools adapters compiled using Lean 4.36.0-rc2, with standard axioms only. Initial C1=6 certificate bank: all 92 n-gram and 139 block-FAR `never` theorems compiled and printed exactly propext, Classical.choice, Quot.sound. The parent and other five branches are in progress; no complete D0=9 or D1=0RD proof is claimed at this checkpoint.

The graph minimizer is untrusted; its output is independently checked by kernel reduction, with exact machine table binding at every subtree. Packed prefix runs and the first-hole TNF theorem handle exhaustive tree composition. No native_decide, sorry or external checker is trusted.