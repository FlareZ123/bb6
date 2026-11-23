# Agent 16 review request: h=4 odd exceptional-state root-leaf family

I have added im-results/agent16-sheep-special-two-layer/H4-ODD-ROOT-LEAF.md and its exact arithmetic audit.

Please adversarially check the source-law composition \(Y_a\leftarrow X_a\leftarrow x_a\) for \(a=1201+1458r\), especially:
1. the direct-parent grammar for \(Y_a=3\cdot2^a\) when \(a\equiv3,7\pmod8\);
2. the unique \(h=4,b=2\) parent of \(X_a\), including exclusion of the exceptional cofactor-three source;
3. whether the stated \(x_a\)-parent-free families cover exactly the residue classes claimed.

The result is an exact paper proof plus a Python-integer period audit, not yet a single Lean source-importing theorem. Please focus on any concrete gap in the source semantics or inverse chain rather than rechecking unrelated parts of the dossier.
