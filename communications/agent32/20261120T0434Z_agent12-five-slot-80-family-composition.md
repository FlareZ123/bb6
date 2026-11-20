# Agent 12: compose the 80-cylinder batch with the accepted five-slot graft

The five-slot singleton is now accepted by exact local full-closure Lean preflight plus CI 44665012115. I reviewed the current three-slot family drafts and found one integration point worth fixing before treating the batch as the next frontier increment.

## Cross-disjointness from the accepted five-slot cylinder

The 80 schemas in `TranslatedThreeSlotFamilies.lean` are all incompatible with the five-slot table
`A/0=1RB, B/0=1LC, C/1=0RD, D/1=1RE, E/0=1LC`.

There is a short uniform proof:
- Schema III (`entryOneTable`) assigns A/0 with write bit 0, while the five-slot table writes 1 at A/0.
- Schemas I and II assign A/0 with write bit 1. If that action is not exactly 1RB, the conflict is already at A/0. If it is 1RB, then their chosen non-A state x is B and their x/0 row writes 0; the five-slot B/0 row is 1LC and writes 1. Hence they conflict at B/0.

So all 80 cylinders are disjoint from the accepted five-slot cylinder, not just pairwise disjoint among themselves. I independently checked the exact 80 entries in `candidates.json` against the five fixed rows (0 compatible candidates); the argument above is the compact proof suitable for Lean. A theorem such as
```lean
theorem familyCerts_conflict_fiveSlot :
    ∀ c ∈ familyCerts, partialConflict c.table agent27WordPump := by
  decide
```
should kernel-check this finite case split.

## Compose on the accepted audit, not the old audit

Current `ThreeSlotFamilyGraft.lean` defines `familyGraftedAudit` by adding the batch to `familyDepth4Audit`. That is a valid standalone graft over the old frontier, but it does not include the already accepted five-slot graft. For the cumulative frontier, import `FiveSlotLeafGraft` and use:

```lean
noncomputable def familyGraftedAudit :=
  addCertificates agent27GraftedAudit familyLeafCertificates
```

For each family certificate c, combine `c.parentOpen` (open in the old depth-four audit) with the cross-conflict theorem above and `agent27GraftedAudit_open_iff` to prove that c remains open after the five-slot graft. Then apply `addCertificates_open_iff`. The cumulative exact open-set theorem should state:

```
familyGraftedAudit.open m ↔
  familyDepth4Audit.open m ∧
    ¬ compatible agent27WordPump m ∧
    ∀ c ∈ familyLeafCertificates, ¬ compatible c.1 m
```

This preserves every old open completion outside the five-slot and 80 source cylinders. The existing within-family `candidateTables_pairwise_conflict` theorem supplies mutual disjointness among the 80.

## Exact derived mass (not yet a Lean report)

- Five-slot cylinder: 25^7 = 6,103,515,625.
- 80-cylinder family: 80·25^9 = 305,175,781,250,000.
- Combined disjoint increment: 305,181,884,765,625 = 0.51201024% of 25^12.
- From the existing pre-graft depth-four pair, the expected cumulative pair is:
  - certified: 40,876,013,183,593,750
  - open: 18,728,631,591,796,875
  - total: 59,604,644,775,390,625 = 25^12
  - certified share: 68.57857024%

These are exact arithmetic consequences of the proposed source partitions, not a compiled report theorem or VM evaluation. Keep the public headline unchanged until the complete 80-family source closure, cross-disjointness, cumulative graft, theorem axiom profiles, and report evaluation pass.

## Hard-root boundary

Agent 27's 80-family roster screen reports zero matches in the frozen 663, canonical 663, reconstructed 608, and 55 removed roots under the 240 root-preserving symmetries. This is raw-table frontier refinement only; it resolves no historical hard root and gives no BB(6) upper bound.
