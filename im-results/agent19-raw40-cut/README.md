# Raw40 parent: exact local frontier and closed subcylinders

Parent `1RB---_1RC---_0RD---_1LD1LA_------_------`, canonical raw40. First unassigned query A1 after six ordinary steps. **The whole parent remains unresolved.** Its two-query-level exact canonical cut has 189 residual five-hole representatives (Raw40CanonicalCut / Raw40LocalCut). The earlier unquotiented 303-cylinder count is a distinct representation. The authoritative global interface is the source-accepted Canonical64 integrated roster; this local dossier does not change its count.

## Established local results

- Round37 (A1=0RD, B1=0RE): exact weighted **214**, attained by `1RB0RD_1RC0RE_0RD0LE_1LD1LA_0RC1LF_0LEHHH` (213 ordinary transitions + halt, delay 0). All 836 open leaves closed: 831 FAR≤5 and five previously saved FAR6 witnesses. All 24 audit shards, empty-residual aggregate, and [exactness](Raw40Round37Exact.lean) passed local Lean 4.36.0-rc2 against Canonical77 artifact 14997966221, using an equivalent standalone generator without unrelated pump imports. [Rebuild](prepare_round37.py). No new global roster count.

- Rounds35–36 (B1=0RC): A1=0RD exact weighted **225**, A1=1RB **219**. The 196 and 178 open leaves reduce respectively to 195 and 177 FAR≤5 certificates plus the previously established A10RC sweep (F0 free). Both enclosing 28-module audits (including base and aggregate), empty residuals, and attaining witnesses compiled in Lean 4.36.0-rc2 with standard axioms only. [Rebuild](prepare_round35_36.py), [R35 exact](Raw40Round35Exact.lean), [R36 exact](Raw40Round36Exact.lean). Local proof generation used an equivalent modular generator and the exact A10RC namespace extracted from `Raw40MoreTwoSided.lean`; the rebuild uses the original full module. The fresh-state-alias nores proof now explicitly reduces `Move.next.val` before `omega`. No global roster decrement or new CI acceptance.


- Rounds22–24 (A1=1RC): C1=1LC exact weighted **96**, C1=1LD **114**, C1=0LD **411**. All 24 audit shards, empty-residual aggregate, and witness exactness per parent compiled locally against Canonical77 artifact 14997966221 with standard axioms only. R22: 763 opens (749 FAR5+14 pumps); R23: 672 opens (655 FAR5+17 pumps); R24: 155 opens (151 FAR5+3 pumps+1 FAR6). [Round22/23 rebuild](prepare_round22_23.py), [Round24/25 rebuild](prepare_round24_25.py), [R22](Raw40Round22Exact.lean), [R23](Raw40Round23Exact.lean), [R24](Raw40Round24Exact.lean).
- New reusable recurrence proofs: [NestedCore](Raw40NestedCore.lean) (11 instances), [PairCore](Raw40PairCore.lean) (8), and [AffineCore](Raw40AffineCore.lean) (2). Common C1=0RC inner sweep converts D(0^a1^(k+1),[]) to B(11,1^(a+3k)); the first two cores give exponential growth n→3n+z+4, the affine variant adds five ones. All 21 instances passed kernel checking. R25 C1=0RC exact **357** was locally kernel-checked in the preceding incarnation, together with R26 C1=0LE **216** and R27 C1=0RE **193**. R28/R29 aggregation and the full A1=1RC consumer remain unaccepted; see [R26–29 rebuild](prepare_round26_29.py) and [A1RC consumer](Raw40A1RC.lean).
- [DigitCore](Raw40DigitCore.lean) establishes three-cell binary counter carry, exact recursive fill and overflow costs, and arbitrarily long live blank prefixes. Six [instances](digit-certs.jsonl) for C1=1LE compiled with propext/Quot.sound only. The R28 enclosing bound 131 is a candidate until aggregation. 

- Round21 (1RC/0LB): exact weighted maximum **101**, attained by `1RB1RC_1RC1RE_0RD0LB_1LD1LA_1LD0RF_HHH0LB` (100 ordinary transitions + halt, delay zero). 274 open search leaves: 254 FAR≤5, 19 [compact pump certificates](round21-pumps.jsonl), and the independently proved [alternating unary sweep](Raw40Leaf236.lean) with blank entry 11 and return cost 48n+66. All 24 audit shards, empty-residual aggregate `Raw40C1RC0LB.all_quotient`, and [exactness](Raw40Round21Exact.lean) passed local Lean 4.36.0-rc2 with standard axioms only, using original Canonical77 artifact 14997966221 (CI45554648116). [Rebuild script](prepare_round21.py). No new CI or global roster count claimed.

- Round20 (1RC/1LB): exact weighted maximum **85**, witness `1RB1RC_1RC0RE_0RD1LB_1LD1LA_0RC1LF_0LEHHH`, 84 ordinary transitions + halt, delay zero. All 81 open leaves closed: 79 FAR≤5, one FAR6, and existing all-time OneRC1LB sweep theorem. All 24 canonical audit shards and [exactness](Raw40Round20Exact.lean) compiled locally against the same Canonical77 dependency artifact as Round16. Local compilation imported the exact OneRC1LB theorem and its private helper extracted from Raw40MoreTwoSided; the [reproduction script](prepare_round20.py) imports the original full module. No new CI or global roster count is claimed.

- Round16 (1RC/0RD): exact weighted maximum **57**, compatible witness `1RB1RC_1RC0RE_0RD0RD_1LD1LA_HHH0RF_0RD1RD`, 56 ordinary transitions + halt, delay zero. All 24 canonical audit shards, empty residual aggregate `Raw40C1RC0RD.all_quotient`, and [exactness](Raw40Round16Exact.lean) compiled locally in Lean 4.36.0-rc2 on Canonical77 artifact 14997966221. The 81 open search leaves have 77 FAR≤5 and four saved larger-FAR certificates. Reproduce the generated parent audit from `prepare_round10-18.py 16` (the local build used the equivalent standalone generator without the empty pump import). No new CI or global roster count is claimed.

- [Round5](Round5-README.md): exact weighted maximum **1891** for 0LA/0LB, with kernel-checked coverage and attainment.

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
