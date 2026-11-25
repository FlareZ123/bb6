# Raw109 membership in the canonical70 roster (intermediate)

This is a focused combinatorial check for an additional possible canonical parent cut. Agent4's Raw109 dossier states the parent table
1RB---_1RC---_0RD---_1LD1RE_---1RB_------
and a candidate complete-parent bound of 1703. The parent source audit is still pending.

Agent8's current champion-independent route constructs a 70-entry roster by grafting raw121 and raw110 onto canonical72. Raw109 is not among those cuts. This module imports that canonical70 roster and Agent4's Raw109Cut, then checks by decidable table equality whether the Raw109 parent remains as an exact entry. If it does, the filter should reduce the count from 70 to 69.

The module deliberately does **not** import or claim Raw109Closed. It only checks membership and count, so it can be compiled before the 13-child Raw109 parent cover is source-accepted. If the membership/count pass and Raw109Closed.all_closed later passes its original-source audit, the standard graftRoster_sound theorem can add a 1703/6766859 mixed-bound soundness result. Combining raw109 with raw112 may yield further reductions if the p112 entries survive; those counts require separate decidable checks.

Status: source draft, not Lean-compiled. The existing canonical70 workflow needs only the generated Raw109Cut data sources (the raw109-cut generator target stages B0LD/B0RE). Do not create a duplicate CI workflow.
