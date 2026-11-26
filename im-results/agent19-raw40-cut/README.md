# Raw40 parent: exact local frontier and closed subcylinders

Parent `1RB---_1RC---_0RD---_1LD1LA_------_------`, canonical raw40. First unassigned query A1 after six ordinary steps. **The whole parent remains unresolved.** Its two-query-level exact canonical cut has 189 residual five-hole representatives (Raw40CanonicalCut / Raw40LocalCut). The earlier unquotiented 303-cylinder count is a distinct representation. The canonical68 global roster remains the authoritative conditional interface.

## Established local results

- [Round4](Round4-README.md): newly complete exact weighted score **334** for the 0LA/1LB five-hole cylinder. All 25^5 completions covered; exact attained witness, locally compiled original dependency artifact and kernel audit.
- [Canonical batch](canonical-batch-notes.md): four exact five-hole maxima 100, 47, 43, 114, and earlier RDLC bound 106 ([RDLC](RDLC-README.md)).
- [Canonical new](Canonical-New-README.md): 17 additional closed canonical cylinders, including RE1RE exact-score case; local kernel acceptance and retained list of 172 from the original 189 (does not subtract the separate batch or Round4).
- [Round3](Round3-README.md): prior complete candidate for 0LB/0RC; its parent audit requires source acceptance.
- [AutoPump](AutoPump-README.md): uniform nonhalting recurrence certificates for further one-hole cylinders. The enclosing candidate parents are not automatically discharged.

## Initial two-query coverage (historical baseline, still mathematically valid)

Three uniform five-hole pump families:

| A1 | Next assigned slot | Entry | Right unary length | Epoch cost |
|---|---|---:|---:|---:|
| 0LA | C1=0RC | 9 | 3n+2 | 6n+13 |
| 1LA | B1=0RD | 8 | 2n+3 | 8n+17 |
| 1LA | B1=1RB | 8 | 4n+3 | 8n+15 |

Raw40Pump.lean and Raw40MorePumps.lean prove these recurrences and universal NeverHalts. Raw40Partial.lean checks the complete two-query partial audit at weighted bound 7014. It retains 303 unquotiented five-hole cylinders; exact raw mass retained 2,958,984,375 of 6,103,515,625. Raw40Graft.lean's older 379-entry conditional frontier is a historical refinement of canonical77, not a current global roster.

All baseline modules compiled locally using Lean 4.36.0-rc2 and coherent original canonical77 artifact 14997966221 (CI45554648116), standard axioms only. Continue local coverage using the existing exact canonical quotient checker and a combined retained-complement consumer; do not infer global closure from a raw assignment count.
