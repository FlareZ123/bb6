# Three-slot translated blank-drift family

## A concrete three-slot cylinder

The smallest prepared example fixes only:

| Input | Action |
|---|---|
| A/0 | 1LB |
| B/0 | 0RA |
| A/1 | 0RA |

The blank-root trace is:

| Successful moves | State | Head | Marked cells |
|---:|---|---:|---|
| 0 | A | 0 | `{}` |
| 1 | B | -1 | `{0}` |
| 2 | A | 0 | `{0}` |
| 3 | A | 1 | `{}` |

After three moves, the machine is back in state A on the blank tape with head displacement +1. The same three-transition macro repeats forever. No other transition input is consulted. Consequently every total completion of this three-slot partial table is nonhalting.

The cylinder has exactly

`25^9 = 3,814,697,265,625`

complete six-state, two-symbol machines.

## Lean artifacts

- `TranslatedThreeSlot.lean` defines the three-slot partial machine and the finite translated check `finiteTranslatedCheck p 0 3`.
- `agent27Three_cover` applies the existing all-completions theorem `finiteTranslatedCheck_sound`.
- `agent27Three_never` specializes the cover at bound zero.
- `ThreeSlotLeafGraft.lean` attempts to prove this entire cylinder is open in the existing `depth4ResidualAudit`, then attaches the source certificate using `addCertificate_open_iff`. The old physical first-unknown path is A/0, B/0, A/1; the three-slot endpoint has no unknown in the 12-step scan.

The exact new Lean files have **not yet passed local compilation**. The source theorem is a Lean proof script, not an accepted compile result. Do not update the global coverage report or promote this to `results/` until the exact dependency closure and axiom output have been checked.

## Bounded search for a larger disjoint family

`search_three_slot_translated.js` is a dependency-free Node.js search/evaluator. It:
1. explores blank-root executions with at most three assigned ordinary transition inputs, at most ten successful moves, entry length at most four, and positive period at most six;
2. records the first nonzero finite-support translation;
3. mirrors the current finite-halt, finite-ray, zero-mask, exact-lasso, and finite-entry-macro decision disjuncts;
4. checks the authentic 12-step physical scan and each prefix's first-unknown/oracle status;
5. checks pairwise transition conflicts between candidate partial tables.

Current runtime output from the same algorithm:
- 22,783 DFS nodes;
- 622 distinct translated candidates before the old-oracle filter;
- 80 candidates surviving the current combined oracle;
- all 80 have exactly three assigned inputs;
- all four prefixes (0 through 3 assigned inputs) reject the old oracle;
- each candidate's first-unknown path exposes its three assigned inputs, then the 12-step scan finds no unknown;
- all 3,160 unordered pairs conflict on at least one common assigned input (zero compatible pairs).

The 80 witnesses split by entry / period / displacement as follows:

| Entry | Period | Displacement | Candidates |
|---:|---:|---:|---:|
| 0 | 3 | +1 | 30 |
| 0 | 3 | -1 | 30 |
| 0 | 4 | +2 | 5 |
| 0 | 4 | -2 | 5 |
| 1 | 3 | +1 | 5 |
| 1 | 3 | -1 | 5 |

If the full 80-candidate list is reproduced and its individual translated checks, parent-open proofs, and pairwise disjointness are accepted in Lean, the union mass is

`80 × 25^9 = 305,175,781,250,000`

or **0.512%** of all `25^12` raw tables. This aggregate is currently computational evidence only, not a Lean-certified family theorem. The concrete first cylinder is the immediately prepared source proof; the remaining 79 and the aggregate disjointness are follow-on work.

## Interpretation

This is a new translated-blank drift certificate, not an exact finite-configuration lasso: the control state and tape return, but the head moves. It is also not captured by the existing fresh-ray macro because the three-step witness initially moves left before moving right. It closes neither all BB(6) machines nor any universal runtime bound.
