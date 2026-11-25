# Raw139 F1 = 1LA (code 2): complete proposed weighted closure

Exact parent: `[7,24,11,24,14,21,3,16,12,11,24,2]`.
Proposed original-source theorem: `BB6.Agent48F1OneLA.all_completions_weighted`, all compatible completions have WeightedBound 290.

## Complete finite partition

16 ordinary 24-way split nodes give 369 terminal nodes: 176 translated cycles, 119 last-hole leaves (maximum query index 284), 49 FAR certificates (one uses six DFA states), and 25 inductive growth certificates. All 25 growth recurrences were accepted by local Lean 4.36.0-rc2 against a copied exact zipper model; these are not yet accepted original-source theorems. No open candidate leaf remains. The original-source audit is dispatched at commit c512623e68b633e28fc140370abee778cfaf0939; do not consume the closure until the audit succeeds.

The last hard leaf H25 has table [7,24,11,19,14,21,3,16,12,11,3,2]. Starting after 64 steps it reaches state E with left zipper 1 and right zipper 0 1^(4+3n) (00111)^(n+1). The complete two-phase recurrence increases n by one in 160*n+138 steps. H7 was resolved by a six-state FAR DFA, [0,1,2,3,4,1,5,3,4,4,0,1] in reverse orientation.

## Reusable discovery and replay

`scan.py` computes the bounded finite partition. `autopump.py` guesses repeating words from observed configurations, then discovers literal block transfers with arbitrary unread tails by treating them as opaque markers. It never uses a finite sample as the proof of a universal recurrence. `recipes.txt` gives 25 compact exact replay recipes, with each integer denoting literal steps and L/R-prefix:cost denoting a one-block sweep candidate. `replay.py` reconstructs the symbolic states, and `emitproof.py` emits rfl proofs of each literal transition, sweepL/R induction, join0 composition, and moveCut rotation equalities. `package.py` closes the finite partition using the original FastThreeHoleAudit API. Local reproduction generates byte-identical Lean files in about three seconds.

Run `bash im-results/agent48-raw139-f1-oneLA/reproduce.sh` from repository root with Lean 4.36.0-rc2. The manual workflow pins the exact source commit, checks generated source hashes, compiles all original source dependencies, and audits all 25 growth/nonhalting theorems and the cover theorem.

This is a single raw139 sibling closure, not a proof of BB(6) or a globally accepted roster reduction.