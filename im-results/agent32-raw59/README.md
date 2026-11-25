# Raw59 six-hole refinement

**Candidate status; original-source verification has not yet accepted this refinement.** Raw index 59 in Agent31's 124-cylinder roster: `1RB---_1RC---_0RD---_1LD1RE_---1LA_------`. A1 is first queried after 7 ordinary steps. It has 25^6=244,140,625 literal completions.

| A1 | Candidate bound | Splits | Cycle leaves | Last-hole leaves | FAR leaves |
|---|---:|---:|---:|---:|---:|
| 0RD | 157 | 632 | 11,674 | 2,778 | 85 |
| 1LC | 84 | 1,066 | 18,816 | 5,525 | 178 |
| 1RB | 135 | 1,398 | 25,275 | 6,231 | 648 + 1 recursive counter |
| 1RD | 93 | 547 | 9,528 | 2,372 | 681 + 1 alternating sweep |
| 0LC | 140 | 1,478 | 25,737 | 7,824 | 432 + 2 sweeps |
| 0RE | 167 | 1,650 | 29,417 | 7,862 | 671 + 1 sweep |
| 0RB | 241 | 1,481 | 26,750 | 7,006 | 306 + 2 ngram |
| 0LD | 125 | 1,413 | 25,038 | 6,748 | 698 + 11 ngram + 5 sweeps |
| 0RA, 1LD, 1RA, 1RE | 395 (nonhalting) | 0 | 1 each | 0 | 0 |

The stock exhaustive generator produced all leaves for all six larger children; the existing and newly generated FAR bank covered 2,695 of their 2,700 previously open leaves. The two manually proved leaves have exact universal growth proofs, locally compiled against the copied zipper semantics. Raw59RBCount.lean proves the recursive three-cell counter (entry 17; epoch 12*2^(n+1)-5 from its cost recurrence). Raw59RDSweep.lean proves the alternating sweep (entry 23; epoch 49+24*n). Their original-source never_of_growth bridges are submitted to CI. Three more one-parameter sweep proofs have local kernel checks and deterministic symbolic recipes for original-source generation (0LC leaves 177,229, 0RE leaf55).. The four direct cycles have (entry,period,direction,boundary)=(0,10,R,0),(11,1,L,-1),(0,10,R,0),(6,2,R,1), respectively. The genuine-halt branch is bounded by the incoming zero-delay graph. The planned refinement removes 11 of 25 equal-mass first-hole branches, retaining 14 exact five-hole children, with total mass 136,718,750. This is a candidate reduction of 107,421,875 literal completions; no closure of the parent cylinder or global BB(6) upper bound.

The new 0RB child is a complete candidate independent of the original six-child refinement. All 308 open leaves have witnesses: 306 FAR masks and two local-window certificates (open indices 66 and 70, widths 9 and 6, respectively 1,371 and 504 abstract states). The generator checks roster digest, counts and certificate identities, then emits the original-source weighted-bound target `Raw59A0RBData.lean`. Its 9,765,625 completions would reduce the retained mass to 126,953,125 if accepted and grafted. The 0LD child is likewise fully covered at candidate level: 698 FAR witnesses, 11 local-window certificates (width at most 8), and five one-parameter sweeps. The sweeps have respective (entry, intercept, slope) triples (15,20,4), (15,24,4), (15,20,4), (13,18,4), (13,22,4). Run `python generate.py 0LD` for that child. Together 0RB and 0LD account for 19,531,250 more literal completions and, if accepted and grafted alongside the previous 11 branches, leave 117,187,500 completions in 12 first-hole children. Until then the existing refinement theorem still retains both. Run `python generate.py 0RB` for the standalone new child, or `python generate.py` for all generated trees. Raw59Refinement.lean retains all other children and all other residual cylinders. Source checking is required before treating these as accepted removals.
The first source run (45521029307) generated the initial two trees successfully but failed on omitted explicit theorem type annotations in Raw59Base.lean; those have been corrected. No claimed source acceptance yet.
