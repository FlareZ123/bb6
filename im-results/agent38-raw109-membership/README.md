# Raw109 membership in the canonical71 roster (intermediate)

This is a focused combinatorial check for an additional possible canonical parent cut. Agent4's Raw109 dossier states the parent table
1RB---_1RC---_0RD---_1LD1RE_---1RB_------
and a candidate complete-parent bound of 1703. The parent source audit is still pending.

The canonical78 base removes eighteen previously covered raw indices; raw109 is not among those eighteen. The canonical72 route removes raw107, raw113, raw114, raw115, raw117 and raw119, and Agent8's canonical71 route additionally removes raw121. The Raw109 parent may therefore be a retained canonical71 representative.

Canonical70Raw109Membership.lean does only two things:
1. Proves exact membership of the Raw109 parent in the canonical71 roster using decidable table equality.
2. Filters that parent and proves the expected 71→70 count.

It does **not** import or claim the Raw109 parent cover. If the membership proof succeeds, then after Raw109Closed.all_closed is source-accepted, the standard graftRoster_sound theorem can turn this into a 70-entry 1703/7014 mixed-bound interface. Combining with raw110 and raw112 would then potentially reduce the residual count to 68.

Status: source draft, not Lean-compiled. Include in the existing Raw109/canonical-roster audit only if the required generated Raw109 sources and canonical71 source manifest are available. Do not create a duplicate CI workflow.
