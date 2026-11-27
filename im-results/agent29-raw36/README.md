# Raw36 cold sibling

**Candidate results, not yet accepted by Lean.** Raw36 is `1RB---_1RC---_0RD---_0LD---_------_------` (eight holes). Its first unknown query is D1 at step 5. Ten ordinary D1 children have direct translated-cycle witnesses; D1=1LB gives the next unknown B1 at step 6, where five more direct cycles apply. Raw36Cut.lean proposes the canonical quotient cut retaining 24 obligations (including the complete-search descendant), preserving all other branches explicitly.

## Complete six-hole descendant
The literal table `1RB---_1RC0LA_0RD---_0LD1LB_------_------` first queries C1 at step 9. The untrusted exhaustive first-hole search across all 24 ordinary C1 children plus its halt branch reports:
- 244,140,625 literal completions, 20,583,715 halting and 223,556,910 nonhalting in the candidate partition.
- 395,640 ordinary-child nodes: 16,484 splits, 288,336 translated cycles, 10,830 FAR closures, 79,990 last-slot closures.
- Zero open leaves; sufficient weighted cutoff 162 including incoming blank delay, not asserted sharp.
- Exact census and DFA codes in candidate.json, generated with search.cjs (cutoffs remain OPEN).

generate.py reconstructs the deterministic trees and checks the census exactly before emitting original Lean Audit terms with the existing FAR mask generator and chunked zipCheck proofs. Selected child: python generate.py 1; all-child invocation emits a composition theorem. Generated proofs remain unaccepted until source audit.
