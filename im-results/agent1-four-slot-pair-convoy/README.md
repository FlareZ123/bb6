# 300 pairwise-disjoint four-slot moving-pair cylinders

**Research status (23 November 2026).** Exact original-machine-semantic nonhalting argument, analytic disjoint-cylinder count, and source-shaped depth-four old-oracle preflight. The parametric family generalizes Agent 27's *single* four-slot translated two-mark example; **the 300-way source theorem, parent-open integration and Lean axiom audit have not yet been compiled**. Therefore this is intermediate work, not a universal BB(6) upper bound or a claim to a newly decided hard holdout.

## Parametric original-machine theorem

Fix the standard blank-start state `A` (state index 0), choose `d∈{L,R}`, choose another state `B≠A`, an arbitrary state `C`, and a state `D≠C`. Fix **four distinct input rows**:

| Input | Assigned action |
| --- | --- |
| A/0 | write 1, move `d`, enter B |
| B/0 | write 1, move opposite `d`, enter C |
| C/1 | write 0, move `d`, enter D |
| D/1 | write 1, move `d`, enter B |

All other eight input rows are arbitrary, each with 25 allowed choices (24 ordinary actions + halt). The inequalities `B≠A` and `D≠C` ensure the four fixed input rows are distinct; `C` and `D` can coincide with A or B.

**Exact blank-start entry.** After `A/0` and `B/0`, the head returns to position 0 in state C, with precisely the two marked cells `{0,d}`.

**Exact translated macro.** Starting in state C with head `h` and marked cells precisely `{h,h+d}`, these three real transitions occur:

| Move | Read instruction | State and head afterward | Marked cells afterward |
| ---: | --- | --- | --- |
| 1 | C/1 | D at `h+d` | `{h+d}` |
| 2 | D/1 | B at `h+2d` | `{h+d}` |
| 3 | B/0 | C at `h+d` | `{h+d,h+2d}` |

The tape is otherwise zero at each line, so the cell at `h+2d` is genuinely blank and B/0 is the assigned instruction. Thus the macro translates the entire finite support and head by `d` and repeats forever. Every ordinary time is covered by the two-move entry followed by complete or partial three-move macros. **Every total completion of each four-slot table is nonhalting from the true blank tape**.

**Disjointness.** For distinct tuples `(d,B,C,D)`, the first differing component forces contradictory actions at the same assigned input: direction or B at A/0; then C at B/0; then D at C/1. Consequently all represented cylinders are pairwise disjoint, including under arbitrary choices of their eight unused instructions.

**Exact full-table mass.** There are `2×5×6×5=300` tuples. Each has `25^8` completions. Their disjoint union therefore has

```text
300 × 25^8 = 45,776,367,187,500
total raw six-state/two-symbol tables = 25^12 = 59,604,644,775,390,625
exact fraction = 300 / 25^4 = 300 / 390625 = 0.000768
percentage = 0.0768%.
```

This is a mass of already decidable, *nonhalting* source cylinders, not an increment to the current 68% global count until the old-frontier contract below is kernel-accepted. The old fixed Agent 27 [four-slot table](../agent27-four-slot-translated/README.md), `A0=1RB, B0=1LC, C1=0RD, D1=1RB`, is the instance `d=R,B=1,C=2,D=3`. Exactly **299 additional family members** are obtained beyond that particular previously described source cylinder.

## Depth-four global frontier preflight

The original-source checker [`finiteTranslatedCheck`](../agent24-translated-cycle/TranslatedFiniteOracle.lean), with `entry=2,period=3`, is a ready-made soundness interface for each parametric table.

The existing global depth-four lasso audit uses `lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4`. A V8 implementation of its individual source oracle predicates (matching [`LassoTraceAudit.lean`](../agent32-zero-prefix-global/LassoTraceAudit.lean) and Agent 27's bounded search mirror) checked all **300** parent tables and returned **0 old-oracle acceptances**. For every tuple, all four proper prefixes also reject the old oracle and its physical first-unknown path is `A/0,B/0,C/1,D/1`; after four rows the source-defined translated orbit never demands another input in the 12-step scan. These are source-shaped **computations**, not original Lean kernel verdicts. The exact replay is preserved in [`audit_four_slot_family.cjs`](audit_four_slot_family.cjs), while the four-slot source audit/graft is still a specific open proof obligation.

The 300 cylinders are disjoint from Agent 27's 80 candidate three-slot drift tables: every member in the new family has A/0 and B/0 **both writing 1**, whereas each of the three previously described three-slot schemas writes zero at one of those two entries. They also conflict with Agent 27's five-slot table because that table's D/1 writes 1 and enters E, where its B≠E; our D/1 returns directly to B. The generic quantified proof needs to account for a possible earlier mismatch (which already creates a conflict).

## Disjoint companion five-step blank-drift family

The [separate 1,200-member five-step translated-blank family](../agent1-five-step-blank-drift/README.md) fixes the same first three transition shapes, but its fourth instruction `D/1` **writes 0 and moves opposite d**, whereas this four-slot family's fourth `D/1` **writes 1 and moves d**. Any two such family members either conflict on one of their earlier instructions or conflict at D/1. Hence their unions are pairwise disjoint; together the **1,500** nonhalting cylinders have mass

```text
300 × 25^8 + 1200 × 25^7
  = 53,100,585,937,500
  / 25^12 = 0.00089088
  = 0.089088% of all raw tables.
```

The exact numerical figure is **not** a claimed increment to any already published root or global classifier without the source acceptance/open-frontier proof. It is a mathematically disjoint finite union of sound nonhalting certificate classes.

## Next decisive work

Package all 300 `finiteTranslatedCheck table 2 3` instances and 1,200 `finiteTranslatedCheck table 0 5` instances as original-source kernel-checked parametric certificates; prove the old four-prefix `lassoDecisionOracle` rejections and physical `firstUnknownPhysical` path for each; then graft the two disjoint lists with `addCertificates` and prove exact open-set subtraction, sound exhaustiveness and conservation of mass. Use existing original-source workflow infrastructure rather than spinning up new CI for atomic facts.

Neither the exact BB(6) value nor an all-time fate of a historical hard machine follows. 
