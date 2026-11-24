# Raw residual 91: complete candidate closure

Canonical residual 58 of the 124-roster: `1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RC`. Four holes, 390625 full assignments (24 moves plus halt per hole).

Deterministic candidate tree: 208 splits including root, 3838 side-cycle leaves, 875 last-hole leaves, 72 other leaves. Of the latter, 71 have finite automata certificates and the remaining leaf has a universal symbolic growth proof. No unresolved candidate leaves.

The proposed weighted bound is 76, attained at 75 ordinary steps plus halt query with zero incoming blank delay by `1RBHHH_1RC1LF_0RD1RD_1LD1RE_0LF0LB_1LA0RC`.

## New symbolic growth

For `1RB1RF_1RC1LF_0RD0LB_1LD1RE_---0LB_1RA0RC`, the zipper family is F with empty left list and right list 10 followed by 5n+5 ones. Blank reaches family 0 after 56 steps. The exact transition from family n to family n+1 costs 56n+103 steps. Decompose into 4 entry steps, n repeated 11-step right sweeps, 18 turning steps, 5n+8 repeated 9-step left sweeps, and 9 final steps. E0 is never consulted. The universal equations compiled locally in Lean 4.36.0-rc2 against a copied core zipper model; original source integration and full roster graft are pending CI, not yet claimed.

## Reproduction

Run generate.py with repository dependencies. It regenerates the tree using the existing enumerator, checks the SHA256 of the open roster, constructs FAR masks, emits 24 independent Lean subtrees and a bound/attainment theorem. Raw91RosterBridge.lean connects the closure to the roster. Use the existing agent13-coverage workflow target weighted-tnf-raw91. No timeout or finite trace alone is counted as a proof.

This is intermediate work toward the global upper bound, not a determination of BB(6).
