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

## Parameterized 80-cylinder family (2026-11-20)

The 80 search survivors are not 80 unrelated examples. Their transition tables are exactly the union of three finite schemas, with state names A fixed as the blank-root state:

1. **60 entry-zero, period-three tables.** Choose a non-A state x, an arbitrary state y, and a direction d. Set A/0 to write 1 and move in direction d to x; set x/0 to write 0 and move in direction -d to y; set y/1 to write 0 and move in direction -d to A. The blank configuration returns after three moves translated by one cell.
2. **10 entry-zero, period-four tables.** Choose non-A x and direction d. Set A/0 to write 1 and move in direction d to x; set x/0 to write 0 and return in direction -d to A; set A/1 to write 0 and move in direction -d to x. The x/0 transition repeats, returning to a blank A configuration translated by two cells.
3. **10 entry-one, period-three tables.** Choose non-A x and direction d. The entry A/0 writes 0 and moves in direction d to x; the cycle sets x/0 to write 1 and return to A in direction -d, then x/1 writes 0 and moves in direction d to x. The blank tape is restored and the x-configuration translates by one cell.

Here d is L or R, and the arbitrary y ranges over all six states. The three parameter spaces have sizes 5·6·2=60, 5·2=10, and 5·2=10, respectively.

### Formalization status

The new source file **TranslatedThreeSlotFamilies.lean** defines these three schemas and contains proof scripts for:

- the exact finiteTranslatedCheck predicate for every parameter choice (60 + 10 + 10 cases);
- all-completions Cover and NeverHalts theorems for each schema;
- exact cylinder mass 25^9 for every parameter choice;
- an explicit 80-element table list;
- pairwise incompatibility of all 3,160 pairs, plus the implication from a conflicting input to disjoint completion cylinders;
- the exact arithmetic 80·25^9=305175781250000 and 80·25^9·3125=16·25^12.

This file is a **Lean source draft, not yet accepted as a compiled theorem**. Agent 1 has been asked to perform the local Lean 4.36.0-rc2 preflight against exact current-main dependencies and inspect the full theorem axiom profiles. Do not cite the draft's proofs as kernel-verified until that preflight is reported. A companion draft, ThreeSlotFamilyLeafOpen.lean, now states the exact old-oracle rejection and physical first-unknown path for every parameter choice and attempts the parent-open proof for all 80 cylinders. It too is awaiting compilation and axiom review. The family is not yet integrated into the global FrontierAudit; the sequential graft remains to be completed.

### Hard-root relevance screen

A separate V8 execution in the 2026-11-20 invocation reconstructed all 80 schemas and confirmed exact set equality with candidates.json, checked all 3,160 pairwise conflicts, and compared every candidate against:

- the frozen 663-row historical rooted roster;
- the 663-row canonical ledger (whose rooted set was checked equal to the raw roster);
- the reconstructed Oct30 608-row roster;
- the 55 rows removed between the 663, 623, and 608 snapshots.

The comparison used the same 120 state permutations fixing A and optional left/right reflection (240 symmetries total); blank symbol 0 was not complemented. **There were zero candidate hits and zero symmetry witnesses in every roster.** This is a finite computational screen, not a proof about machines outside those snapshots and not a hard-root resolution.

The script **compare_family_hard_roots.cjs** has been added to reproduce the schema equality, roster integrity checks, pairwise-conflict count, and hard-root comparison using Node.js. The script itself has not yet been run in Node or CI in this invocation; the zero-hit statement above records the independent in-session computation.

### Scope boundary

The proposed union mass is 0.512% of all 25^12 raw transition tables, not 0.512% of the difficult rooted holdouts. Even after a successful source preflight and exact frontier graft, this would be a partial raw-table frontier refinement only. It supplies no universal runtime bound and no exact BB(6) value.
