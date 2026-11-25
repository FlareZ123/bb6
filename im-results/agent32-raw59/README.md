# Raw59 six-hole refinement

**Candidate status; original-source verification has not yet accepted this refinement.** Raw index 59 in Agent31's 124-cylinder roster: `1RB---_1RC---_0RD---_1LD1RE_---1LA_------`. A1 is first queried after 7 ordinary steps. It has 25^6=244,140,625 literal completions.

| A1 | Candidate bound | Splits | Cycle leaves | Last-hole leaves | FAR leaves |
|---|---:|---:|---:|---:|---:|
| 0RD | 157 | 632 | 11,674 | 2,778 | 85 |
| 1LC | 84 | 1,066 | 18,816 | 5,525 | 178 |
| 0RA, 1LD, 1RA, 1RE | 395 (nonhalting) | 0 | 1 each | 0 | 0 |

The stock exhaustive generator produced all leaves for both larger children, and the existing FAR bank covered all 263 previously open leaves. The four direct cycles have (entry,period,direction,boundary)=(0,10,R,0),(11,1,L,-1),(0,10,R,0),(6,2,R,1), respectively. The genuine-halt branch is bounded by the incoming zero-delay graph. The planned refinement removes 7 of 25 equal-mass first-hole branches, retaining 18 exact five-hole children, with total mass 175,781,250. This is a candidate reduction of 68,359,375 literal completions; no closure of the parent cylinder or global BB(6) upper bound.

Run python generate.py to regenerate the two exact trees and FAR proof masks, pinned to the observed open-roster digests. Raw59Refinement.lean retains all other children and all other residual cylinders. Source checking is required before treating these as accepted removals.