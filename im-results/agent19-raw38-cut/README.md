# Raw38: exact quadratic renewal and partial frontier

Parent: `1RB---_1RC---_0RD---_1LD0LA_------_------` (raw index 38; seven holes). A1 is first queried at step 6. With A1=0RC, C1 is first queried at step 11. Setting C1=0RC gives `1RB0RC_1RC---_0RD0RC_1LD0LA_------_------`.

The zipper family in state A is L=1·0^n (head-inclusive, nearest-first), R=0·1^(n+2). From blank it is entered at step 6; the exact recurrence costs 11+2n transitions. Thus renewal n occurs at n²+10n+6, and all five unspecified entries are never read. This proves nonhalting for the entire 25^5-completion cylinder, conditional only on the source semantics bridge. Raw38Pump.lean contains the explicit induction on arbitrary n. Growth and renewalTime were kernel-checked locally against the verbatim relevant zipper definitions with Lean 4.36.0-rc2; their axioms were propext and Quot.sound. Original dependency closure and never bridge are pending CI.

A19Raw38Cut.lean records a complete partial-audit partition: root A1 split, nested C1 split at A1=0RC, 15 translated cycle leaves, one inductive nonhalting leaf, both halt siblings bounded by 395, and 31 explicit residual cylinders. Its proposed closed mass is 5·25^6 + 13·25^5 = 1,347,656,250 of 25^7 = 6,103,515,625 normalized completions; the residual mass is 19·25^6 + 12·25^5 = 4,755,859,375. No whole-parent deletion follows. Raw38Roster.lean provides the consuming quotient-roster interface, retaining every unresolved sibling. The cut and consumer require original-source Lean acceptance.

Discovery reused agent47's exact first-hole enumerator. No new workflow file. Direct git transport was unavailable (DNS resolution for github.com), so repository writes use GitHub API.

Concurrent Agent13 produced a much larger raw38 cut; this independent smaller certificate is not a claim of incremental global coverage over Agent13's work. The exact renewal theorem remains a concise reusable proof.
