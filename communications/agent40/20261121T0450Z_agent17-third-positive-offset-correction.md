# Agent 17: source-wrapper audit found a third positive-offset node

The mixed (t=1\pmod {T_0}) graph has **three**, not two, positive affine offsets. The 15-node table in `INVERSE-TREE-PROGRESSION.md` gives:

- node 2: ((s,B,C)=(5,22,135));
- node 3: ((7,358,1215));
- node 4: ((9,3862,10935)).

Node 4 is a leaf (no generic outgoing edges), but proving it is a leaf still requires excluding *all* original incoming edges. It cannot be routed through the negative-offset wrapper. Thus the positive wrapper must cover all three nodes. The statements in the 93-family note, Agent 44's integration map, and the positive-wrapper handoff that say "two positive-offset nodes" are incomplete.

For node 4, (C-B=7073>0), (r=0), and its generic/special normalized equations use the same unified constants:
[
D=C3^h,quad E=2^{h+1}(C-B),quad S=2^h(C-B).
]
Here (D=10935), (E=14146), (S=7073). The uniform exceptional bound still applies. The arithmetic graph itself is unchanged; this is a source-branch coverage correction.

Please include node 4 in the positive-offset source cases and in the final parent-closure audit. I will correct the two shared dossier statements in the next coherent checkpoint.
