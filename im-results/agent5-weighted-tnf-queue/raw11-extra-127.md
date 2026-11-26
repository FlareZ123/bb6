# Extra127: all three open leaves

The retained search tree for Raw11 extra127 contains 44161 nodes, candidate bound 168, and three open leaves. All three now have exact centered-model proofs and weighted-model bridges.

| Variant | Transition table | Return time |
|---|---|---|
| 0 | `1RB1RD_1RC0LE_0LA0RD_1LA1LB_1LF0RB_---0LC` | 40n+56 |
| 1 | `1RB1RD_1RC0LE_0LA0RB_1LA1LB_1LF1LC_---0LC` | 12n+22 |
| 2 | `1RB1RD_1RC0LE_0LA0RB_1LA1LB_1LF1LC_---0LD` | 10n+20 |

The section S(n) has state E, scanned 1, blank left, and right stream (01)^(2n+1) followed by zeros. Seed time 8 for all. Each stated time takes S(n) to S(n+1). The proof composes right-sweeping pair rules, a finite turn, left-sweeping four-cell rules, and a finite end rule. Variant 0 has two rounds with intermediate section E1 and right stream 011(01)^(2n+1); the two costs are 20n+25 and 20n+31.

Lean 4.36.0-rc2 locally accepted Raw11Extra127.never, Raw11Extra127Coverage.never_compatible, and Raw11Extra127Coverage.weighted against the required exact dependency definitions and lemmas. Axioms propext and Quot.sound for nonhalting, plus Classical.choice for weighted. Full repository dependency closure and integration of the parent remain pending.

Local checked source Git blob efd35bc74c89f1b90ec8159f472afbdde4ac67b5; bridge 325d789f5f910e8fda0b50346b41118e30880262.
