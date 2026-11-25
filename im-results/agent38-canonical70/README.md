# Canonical 70 cross-route roster (intermediate)

**Status: source draft; not accepted by Lean CI.** This is a conditional root-frontier reduction, not a BB(6) upper bound.

## Construction

Two independent canonical-roster programmes share the raw114 and raw117 parent cuts:

- Agent47's raw110 route removes raw107, raw114, raw117, raw112, and raw110, yielding a proposed 73-roster.
- Agent8's route removes raw113, raw114, raw115, raw117, and raw119, also yielding a proposed 73-roster.

The union has eight distinct parents, so grafting raw119, raw115, and raw113 onto Agent47's 73-roster should leave **70** canonical residual representatives. Canonical70CrossRoute.lean states the exact list, its count, the mixed-bound soundness theorem, and a conditional exact-BB(6) consumer.

## Threshold bridge

The raw110 complete-parent certificate has bound 6,766,859 (source-accepted in run 45597857116). The champion's exact score is proposedTM63Moves + 7. The module includes a small lower-bound lemma showing that the first source section increment alone exceeds 6,766,859:

proposedIncrementCost 2 7 6 63 = 6·4^63 + 42·2^63 + 15 + 8 + 72 + 12·v₂(7) − 9·63.

This avoids normalizing the complete three-section score. The lemma is still awaiting source compilation.

## Proof dependencies and current acceptance boundary

The 70-count and soundness depend on these parent/source results:

| Parent | Bound | Current evidence |
|---|---:|---|
| raw107 | 815 | Source-accepted parent closure |
| raw114 | 7,014 | Source-accepted canonical77 graft |
| raw117 | 1,291 | Source-accepted six-hole cylinder |
| raw110 | 6,766,859 | Source-accepted complete parent closure, run 45597857116 |
| raw112 | 100,000 | Parent-closure source audit pending |
| raw113 | 2,674 | Original-source audit pending |
| raw115 | 458 | Original-source audit pending |
| raw119 | 572 | Original-source audit pending |

The raw114/raw117 overlap is intentional; all other parent tables must be shown distinct in the Lean count. The module uses sequential graftRoster_sound transport and the raw113 generic graft theorem, rather than assuming that two separate 73-counts can simply be added.

exact_from_canonical70_at_champion_score is conditional on Covers for all 70 residuals at the attained champion score. It is **not** a claim that these Covers exist, and it does not determine BB(6).

## Next

1. Obtain successful original-source audits for raw112, raw113, raw115 and raw119.
2. Add this module to the existing shared canonical-graft source workflow (do not create a duplicate workflow).
3. Compile the exact imported closure and audit all exported theorem axiom sets; reject sorryAx and native_decide.
4. Only then update the human-facing frontier synthesis. Keep this work in im-results/ until it contains a genuinely publishable mathematical result.
