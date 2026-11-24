# Raw residual 87: complete candidate closure

Table `1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RB`. Four holes, 390625 full assignments.

Candidate tree: 132 splits including root, 2394 side-cycle leaves, 535 last-hole leaves, 107 FAR leaves, one universal symbolic pump. No unresolved candidate leaves. Weighted bound 108 (candidate maximum from 106 ordinary steps + halt query + one incoming delay).

## New pump

For `1RB---_1RC1LF_0RD0LA_1LD1RE_0RC0LB_0LB0RB`, blank reaches F with empty left zipper and right list (1010)^(n+1)101 at n=0 after 30 steps. The exact transition from family n to n+1 costs 12n+32 steps. Enter C in two steps, translate n+1 right blocks from 1010 to 1101 in six steps per block, turn in 12 steps, and translate n+2 left blocks back in six steps per block. The A1 hole is never consulted. The universal equations compiled locally with Lean 4.36.0-rc2 against a copied core zipper model, with only propext and Quot.sound. The source-integrated pump and full audit are pending CI.

Run generate.py for reproducible candidate generation and the existing agent13-coverage workflow target weighted-tnf-raw87 for source-integrated proof. The roster bridge removes the exact matching table only if all audit checks and the theorem compile.
