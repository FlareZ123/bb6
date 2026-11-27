# Raw36 cold sibling

**Candidate results, not yet accepted by Lean.** Raw36 is `1RB---_1RC---_0RD---_0LD---_------_------` (eight holes). Its first unknown query is D1 at step 5. Ten ordinary D1 children have direct translated-cycle witnesses; D1=1LB gives the next unknown B1 at step 6, where five more direct cycles apply. Raw36Cut.lean proposes the canonical quotient cut retaining 24 obligations (including the complete-search descendant), preserving all other branches explicitly.

## Complete six-hole descendant
The literal table `1RB---_1RC0LA_0RD---_0LD1LB_------_------` first queries C1 at step 9. The untrusted exhaustive first-hole search across all 24 ordinary C1 children plus its halt branch reports:
- 244,140,625 literal completions, 20,583,715 halting and 223,556,910 nonhalting in the candidate partition.
- 395,640 ordinary-child nodes: 16,484 splits, 288,336 translated cycles, 10,830 FAR closures, 79,990 last-slot closures.
- Zero open leaves; sufficient weighted cutoff 162 including incoming blank delay, not asserted sharp.
- Exact census and DFA codes in candidate.json, generated with search.cjs (cutoffs remain OPEN).

generate.py reconstructs the deterministic trees and checks the census exactly before emitting original Lean Audit terms with the existing FAR mask generator and chunked zipCheck proofs. Selected child: python generate.py 1; all-child invocation emits a composition theorem. Generated proofs remain unaccepted until source audit.

## D1=1LB: complete candidate closure of the seven-hole branch

The three follow-up JSON files record ten more ordinary B1 descendants with zero OPEN nodes and four fresh-E descendants with zero OPEN nodes. Together with B1=0LA (candidate.json), the five directly cyclic B1 choices, the immediate B1 halt and four symmetry-equivalent F choices, the entire seven-hole cylinder is covered at candidate level. The full ordinary-move census after E/F transport is:

| Classification | Literal completions |
|---|---:|
| Halting | 615,712,761 |
| Nonhalting | 5,487,802,864 |
| Total | 6,103,515,625 = 25^7 |
| OPEN | 0 |

The 15 searched canonical B1 branches required 4,862,174 candidate nodes, excluding the immediate B1 split and the five direct cycles. Sufficient weighted cutoff **166**. The multiplicity-two entries are B1=0LE,0RE,1LE,1RE, with unused E/F labels exchanged. The other 11 searched B1 assignments have multiplicity one. Counts concern literal completions with 24 ordinary transitions + one halt, not canonical orbit counts.

This closes one entire D1 ordinary branch computationally, not the parent. The direct-cycle D1 and B1 cut is drafted in Raw36Cut.lean; the first independent five-hole proof generator is ready. Three preliminary CI invocations failed before Lean because of metadata field alignment, parser terminator formatting and missing generated imports respectively; all three blockers were fixed in the subsequent revision. Do not mark any new source theorem accepted until the Lean run succeeds. Source acceptance of all 4.86M candidate nodes will require efficient sharding or a compressed semantic checker, not blanket claims from the census.
