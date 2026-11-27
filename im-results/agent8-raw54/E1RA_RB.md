# Raw54 E1=0RA and 0RB — discovery and exact individual certificates

Both are six-hole cylinders. Frozen first-hole enumerator and original bank as in E1RC.

| E1 | split | cycle | last | open | original bank hits | original misses |
|---|---:|---:|---:|---:|---:|---:|
| 0RA | 28565 | 503924 | 139138 | 13934 | 13361 | 573 |
| 0RB | 34061 | 610985 | 156949 | 15470 | 14713 | 757 |

Frozen miss.txt SHA-256: RA 3a2e7cad73a90d8cf34cec12b381383a04232374fddf4539f5d7925ffd3020b6, RB 737cd2d6481e75565cee1301e952609b5e2a7c7ec3da26cc552adec4cf4ffe40. Early first-hole weighted scores max 839 and 842 respectively; not full thresholds.

## Exact shared triple sweep: RA 1,2,3

[Raw54E1RATriple123.lean](Raw54E1RATriple123.lean) exports `BB6.Agent8Raw54.E1RATriple123.never` for each variant of the partial machine:
- 1: `1RB0LB_1RC0LA_0RD0RF_1LD0LE_1RB0RA_---0LB`
- 2: `1RB0LB_1RC0LA_0RD1RF_1LD0LE_1RB0RA_---0RB`
- 3: `1RB0LB_1RC0LA_0RD1RF_1LD0LE_1RB0RA_---0RD`

All start at A with left zipper 00, right 11 after seven transitions. For arbitrary n, the section family is A(00,11(111)^n). A nine-step entry moves to B(01,(111)^(n+1)); a rightward sweep of n+1 triples transfers the triples from right to left in 7(n+1) or 5(n+1) steps depending on variant. A six-step turn reaches A(00(111)^(n+1),11). Each 27-step drain transfers one triple to the right; n+1 drains reach the next section. Total costs 34n+49 (variant 1) and 32n+47 (variants 2/3). Arbitrary-tail equalities and induction justify all lengths, including blank boundary. The named theorem compiled locally in Lean 4.36.0-rc2 using exact original SweepPumping from accepted artifact 15143833177; axioms only propext and Quot.sound. All 25 possible F0 assignments per variant are nonhalting. No aggregate Cover is claimed.

## Frozen candidate ledger
[e1ra-ledger.txt](e1ra-ledger.txt) and [e1rb-ledger.txt](e1rb-ledger.txt) contain disjoint exhaustive classifications of the original misses. RA: 245 FAR, 185 sparse n-gram, 3 proved symbolic, 140 remaining; RB: 276 FAR, 248 sparse n-gram, 233 remaining. Additional FAR code pool consists of the lexicographically sorted union of F codes in e1rc/e1re/e1rf/oneRA ledgers and zeroRB-far-groups minus original bank. Sparse search tries widths 3,4,5,6,7,8,9,10,12,14,16,18,20,24,28 with original two-million-state cap and stops on cap. Each N row regenerates via the existing ngram_sparse.cpp. F/N entries are candidate certificates and must be independently kernel-checked by the future full Cover generator; only P denotes an accepted individual Lean theorem.
