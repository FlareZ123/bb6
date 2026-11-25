# Raw41: two-query sound partition and canonical graft

Parent: `1RB---_1RC---_0RD---_1LD1RA_------_------`, seven unassigned entries. First query A1 at step 6. No assumptions about completions.

The checked two-level tree has 6 first-level cycle leaves, 1 immediate halt case, 18 second-level halt cases, 166 second-level cycle leaves, 5 second-level FAR leaves, and 261 unresolved five-hole cylinders. The closed physical completion mass is 3,554,687,500 of 6,103,515,625 (58.24%); the unresolved mass is 2,548,828,125. These combinatorial masses are calculated from the exact disjoint query branches, not a formally checked count of arbitrary machine symmetries.

All 5 FAR leaves are uniform over 25^5 completions each:
| A1 | Second query | DFA code |
|---|---|---|
| 0LB | B1=0LA | 0012101 |
| 0RC | C1=0RC | 000 |
| 1LA | B1=0LD | 00101 |
| 1LA | B1=1RB | 000 |
| 1RC | C1=0RC | 000 |

Raw41LBLA.lean proves the first FAR leaf directly. Run `python generate_two.py` in this directory to generate Raw41TwoCut.lean (git blob 304db79da478cbff3010ca3c6528cc9c0414f55a). The generator is untrusted; every resulting cycle, FAR certificate, query split, and residual count is checked by Lean. The proved statement is `∀ m, compatible parent m → WeightedBound 16 m ∨ ∃ e ∈ residuals, compatible e.2 m`.

Raw41CanonicalCut.lean uses Agent19's CanonicalPartial checker and proves general `canonical_of_partial`: an ordinary checked tree is also a checked canonical tree, so existing certificate checks need not be repeated. The quotient leaves number 153 rather than 261; replacing the unique Raw41 parent in the accepted 77 roster gives 229 representatives, all other 76 unchanged. The graft retains the global bound 7014 conditional on the explicit unresolved leaves; it is not a proof of BB(6).

Verified locally in Lean 4.36.0-rc2 against accepted canonical77 artifact 14997966221 (CI run 45554648116), with a local import-minimized copy of Agent19's CanonicalPartial source (same definitions/proof, imports CanonicalFrontier, PartialAudit, ZipPrefixAudit rather than Raw40Partial). Compile Raw41LBLA, generated Raw41TwoCut, CanonicalPartial, then Raw41CanonicalCut on a coherent LEAN_PATH. All printed axiom sets are subsets of [propext, Classical.choice, Quot.sound]. No new full-repository CI run has been completed. The generator's raw and canonical counts are independently checked for the unresolved list lengths by Lean.

Next: close the 153 canonical five-hole residuals. Avoid rechecking the already discharged two-level branches. Candidate bank discovery can use the existing FAR implementation in agent19-raw40-cut and agents' other checked candidate banks.