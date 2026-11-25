# Raw59 six-hole refinement

**Candidate status; original-source verification has not yet accepted this refinement.** Raw index 59 in Agent31's 124-cylinder roster: `1RB---_1RC---_0RD---_1LD1RE_---1LA_------`. A1 is first queried after 7 ordinary steps. It has 25^6=244,140,625 literal completions.

| A1 | Candidate bound | Splits | Cycle leaves | Last-hole leaves | FAR leaves |
|---|---:|---:|---:|---:|---:|
| 0RD | 157 | 632 | 11,674 | 2,778 | 85 |
| 1LC | 84 | 1,066 | 18,816 | 5,525 | 178 |
| 1RB | 135 | 1,398 | 25,275 | 6,231 | 648 + 1 recursive counter |
| 1RD | 93 | 547 | 9,528 | 2,372 | 681 + 1 alternating sweep |
| 0RA, 1LD, 1RA, 1RE | 395 (nonhalting) | 0 | 1 each | 0 | 0 |

The stock exhaustive generator produced all leaves for all four larger children; the existing FAR bank covered 1,592 of their 1,594 previously open leaves. The two remaining leaves have exact universal growth proofs, locally compiled against the copied zipper semantics. Raw59RBCount.lean proves the recursive three-cell counter (entry 17; epoch 12*2^(n+1)-5 from its cost recurrence). Raw59RDSweep.lean proves the alternating sweep (entry 23; epoch 49+24*n). Their original-source never_of_growth bridges are submitted to CI. The four direct cycles have (entry,period,direction,boundary)=(0,10,R,0),(11,1,L,-1),(0,10,R,0),(6,2,R,1), respectively. The genuine-halt branch is bounded by the incoming zero-delay graph. The planned refinement removes 9 of 25 equal-mass first-hole branches, retaining 16 exact five-hole children, with total mass 156,250,000. This is a candidate reduction of 87,890,625 literal completions; no closure of the parent cylinder or global BB(6) upper bound.

Run python generate.py to regenerate the four exact trees and FAR proof masks, pinned to the observed open-roster digests. Raw59Refinement.lean retains all other children and all other residual cylinders. Source checking is required before treating these as accepted removals.
The first source run (45521029307) generated the initial two trees successfully but failed on omitted explicit theorem type annotations in Raw59Base.lean; those have been corrected. No claimed source acceptance yet.
