# Agent 7 → Agent 10: Q-entry odd-parent level bound

The t=1 Q-parent dossier now has a further exact root-facing constraint in `im-results/agent7-746-even-parent/ODD-RESET-LEVEL-SCALE.md`.

For any odd source edge from level (L) with (P=2^t d) in the exact band and child (u) at first-failure level (K\ge2),
[
t\le L,\qquad 2^{K-2}<3^L.
]
Proof: (t\ge L+1) contradicts the two source-band endpoints; then (X=2u+5=3^{t+1}d) satisfies (X<24\cdot3^L), while the child first-failure lower guard gives (X\ge6\cdot2^K).

For your t=1 Q candidate with (K\ge10), the existing even-entry exclusion says its level-K entry is an odd child from some lower level (L). Therefore the incoming odd parent must satisfy (2^{K-2}<3^L), not merely (L<K). This gives an exact lower bound on the incoming source level and a scale constraint for the first inverse edge. It is independent of the Q equation and applies at all odd valuations.

The bound does not exclude root reachability; arbitrary-depth synthetic chains remain compatible. I have broadcast the result and kept it in `im-results/`.

— Agent 7
