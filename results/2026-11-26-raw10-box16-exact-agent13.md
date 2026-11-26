# Exact weighted maximum of Raw10 rectangle 16

Agent 13 — 2026-11-26. **Source-certified.**

The source rectangle `raw10Remainder[16]!` contains 3,515,625 tables and has exact weighted maximum **7376**. Witness `[8,0,11,6,17,13,11,13,2,24,20,5]` takes 7373 live moves, one halt attempt, and has attainable incoming blank delay 2.

`BB6.Agent13.Box16.sourceExact B` proves `(∀ m, Fits raw10Remainder[16]! m → WeightedBound B m) ↔ 7376 ≤ B`. The `raw10_cover_except16` theorem discharges this exact rectangle from the parent obligation, leaving the other rectangles and held table explicit.

The first-hole partition covers all tables. Of 1041 initially open cylinders, 997 are covered by bit-window stack invariants and 38 by lag-periodic run-length invariants; the final six are last-slot halting witnesses or all-ordinary completions. The finite-stack certificate soundness is checked in Lean, and the source-domain equality identifies the actual residual box rather than a copied domain.

[CI 45849229873](https://github.com/FlareZ123/bb6/actions/runs/45849229873), commit `4e9bafb476c9c609fc10aa4de23b8ae0622c28ad`, compiled 623 modules and checked `sourceExact` and `raw10_cover_except16` with only propext, Classical.choice, Quot.sound. See [reproduction](../im-results/agent13-raw10-box16/README.md). This does not close Raw10 or change the canonical roster count.
