# Box27 E/F quotient and exact first-query terminal bank

**Status:** source-connected proof candidates, not yet accepted by Lean CI. The numerical count below is an independently computed finite union of cylinder keys, conditional on acceptance of the referenced source theorems. It is not a new global bound on BB(6).

The original 20 D0 choices and seven independent 25-code slots give 122,070,312,500 physical completions. A1,E1,F1 are unconstrained by the earlier five-coordinate bank. Relabel E↔F, including both source slots and target states. The Box27 domain is invariant, since A0/B0/C0/C1 have no E/F targets and D0 allows both four-code E/F target blocks. Root A is fixed. Weighted halting time is invariant under this relabeling by the existing WeightedSymmetry theorem. Hence one can safely take the union of a covered predicate with its conjugate, without new FAR search.

At the first query following D0 there are 137 immediate terminal children: 14 halt after four or five live moves, 123 exhibit an exact translated cycle. Each fixes two independent coordinates and therefore covers 25^6 physical tables. The 14 halt children are especially important: a nonhalting FAR bank cannot certify a genuine halter. All witnesses use the original leaf checker rather than a finite-time heuristic. Box27EarlyTerminal.lean contains the explicit bank and source lift. Box27Symmetry.lean transports any valid five-coordinate predicate; Box27SymmetryFrontier.lean instantiates the previous union.

Exact projected counts (coordinate order D0,D1,E0,B1,F0; 20×25^4 = 7,812,500). Each row represents 25^3 physical completions.

| Candidate union | Projected keys | Physical completions |
|---|---:|---:|
| Prior Box27Partial6452 | 5,040,625 | 78,759,765,625 |
| E/F closure of prior union | 5,168,125 | 80,751,953,125 |
| E/F closure plus terminal bank | 5,386,875 | 84,169,921,875 |
| Residual | 2,425,625 | 37,900,390,625 |

The last union covers 68.952%, a gain of 346,250 projected keys / 5,410,156,250 physical tables. No cylinder multiplicities are summed: enumeration marks the Boolean union. The exact source checker must accept both the prior bank and the new lemmas before this percentage can be reported as theorem-backed.

The six fast D0 values are separate. Of 350 first-query children of the remaining 14 D0 codes, the union exhausts 139 whole children (137 direct, plus D0=14/D1=17 and its conjugate 21), leaving 211. The next target is a complete exact source-backed residual child, not more unstructured global percentages.

## Acceptance plan

Run the existing shared manual source-closure workflow on Box27EarlyTerminal.lean, then Box27Symmetry.lean, then Box27SymmetryFrontier.lean. The latter additionally depends on the older Box27Partial6452 chain; do not treat the arithmetic replay as Lean acceptance. The E0=22 child check 46113905945 succeeded; the aggregate D17 parent join 46114149252 was cancelled, so the old parent remains a candidate until accepted.
