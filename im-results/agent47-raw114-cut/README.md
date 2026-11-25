# raw114: four complete candidate child audits

Status: **candidate**, not yet source-accepted. Parent `1RB---_1RC---_0RD---_1LD1RE_---0LD_------` is a retained canonical78 representative. Its first missing row is E0 after 8 moves.

Full bounded classifier replay (25^6 = 244,140,625 completions): 15,723 splits, 283,208 side cycles, 69,504 last-hole leaves, 8,918 open leaves. Open completion mass 2,652,950; largest discovered weighted halt score 563. Seed-first FAR search found witnesses for 8,671 of the open tables using <=6 DFA states; 247 remain unresolved. This is a search result, not a universal bound.

Four entire E0 branches have complete candidate data:
| E0 | splits | cycles | last holes | FAR |
|---|---:|---:|---:|---:|
| 0LB | 810 | 15221 | 2964 | 446 |
| 0LC | 758 | 13981 | 3271 | 183 |
| 0RC | 521 | 9579 | 2194 | 211 |
| 1LC | 1108 | 20288 | 4974 | 223 |

Reproduce using `python im-results/agent47-raw114-cut/generate_far_cut.py 0RC` (or all four arguments). The 33-code bank covers all 1,063 FAR leaves in these branches. Generator checks open roster hashes, generates exact FAR masks using the repository checker data generator, and emits 24 independently checkable grandchildren per E0 branch plus a universal weighted7014 theorem. All generated audit leaves must be kernel checked; search success alone is insufficient.

Eight other E0 branches are immediate cycle candidates: 0LD,0LE,0RD,0RE,1LD,1LE,1RD,1RE. Combined with four full branch proofs and the immediate halt, this would discharge 13/25 of the parent's raw completion mass. The other 12 ordinary children must remain. The earlier two-level cut (generate.py) is independent; overlapping closures must not be double-counted.

The new generic CanonicalRosterRefinement.lean connects a physical refinement to an existing quotient roster with root-fixing renaming. Its theorem was syntax/type preflighted on a Lean interface fixture; original-source acceptance still required.
