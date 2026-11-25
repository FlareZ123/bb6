# Raw112 membership in the canonical70 roster (intermediate)

Agent31's champion-independent canonical74 construction proves that the raw112 parent removes one entry from the canonical75 roster (which already includes the raw117 cut). Agent8's canonical70 construction further removes raw113, raw115, raw119, raw121 and raw110. Those are distinct parent tables from raw112, so the expected result is that one raw112 representative remains and the 70-entry canonical70 roster can be reduced to 69.

Canonical69Raw112Membership.lean checks this exact membership and count by decidable table equality. It imports Raw112Base only, not the pending Raw112ClosedCover, so the combinatorial question can be settled independently of the parent source audit. If the count proof passes, then after Raw112ClosedCover is source-accepted, the standard graftRoster_sound theorem can use the raw112 parent cover at bound 100,000 to produce a 69-entry 100,000/6,766,859 mixed-bound interface.

Status: source draft, not Lean-compiled. Include it in the existing canonical70 workflow with the Raw112Base source already staged; do not create duplicate CI.
