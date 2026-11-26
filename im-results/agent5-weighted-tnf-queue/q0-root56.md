# q0 active root 56: exact alternating-sweep nonhalting leaf

The six-hole parent is `1RB1RD_1RC---_0LA---_1LA0RE_------_------`, active index 56 in the exact q0 checkpoint (run 45522264094).

The full original-direction first-hole search has 360361 nodes: 251964 translated side recurrences, 8392 coarse MITM closures, 15015 internal splits, 84919 short last-hole leaves, and 71 remaining leaves. Every internal split enumerates all 24 ordinary transitions. Of the 71, 68 have additional finite FAR candidates checked by original-direction stack closure and totalized MITM; two last-hole traces reach F1 at 12327 and 12063 ordinary steps; the remaining machine has the exact proof below. Thus candidate weighted ceiling 12333. Original source checking and roster consumption remain pending.

The remaining leaf is `1RB1RD_1RC0LC_0LA1LB_1LA0RE_1LB1RF_0RA---`. Let A(n) have state A, scanned 0, zero left half-tape, and right half-tape 00(10)^(2n+1)1 (nearest first), zero padded. Step 14 reaches A(0). For every n the exact return from A(n) to A(n+1) takes 14n+28 ordinary steps: enter F (8), n six-step right sweeps, F tail (6), 2n+2 four-step left sweeps, B tail (6). Consequently the section times 14+7n(n+3) are unbounded. The proof establishes no F1 query at any finite step.

Root56.lean was checked locally with Lean 4.36.0-rc2 on 2026-11-26. Root56.advance and Root56.never use only propext and Quot.sound. The semantic bridge Root56Coverage.lean was checked with Lean 4.36.0-rc2 against the accepted Canonical77 WeightedTNF core (artifact 14997966221, run 45554648116). Root56Coverage.never_compatible has axioms propext and Quot.sound; Root56Coverage.weighted has axioms propext, Classical.choice and Quot.sound. It establishes Cover (WeightedBound B) for every B for this exact one-hole leaf. The full parent bound remains a candidate pending exhaustive tree checking.

Root55 and 58 complete candidate scans have 601969 and 405841 nodes, with 243 and 185 open leaves respectively. Root57 scan was interrupted; no coverage claim.
