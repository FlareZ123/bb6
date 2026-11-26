# LF1 late single-hole family

These three residuals have one undefined slot, B1. Starting on the blank tape, the exact first-query counts are:

| Leaf | Table | Steps before B1 |
|---|---|---:|
| 86 | `1RB1LF_1RC---_0RD1RC_1LD1RE_1LC0RA_0LA0LF` | 3055744 |
| 109 | `1RB1LF_1RC---_0RD0LD_1LD1RE_1RC0RA_0LA0LF` | 2298758 |
| 122 | `1RB1LF_1RC---_0RD1RC_1LD1RE_1RC0RA_0LA0LF` | 2295586 |

Each reaches B1 after 1193 accelerated sections. Encode the right word by counts of zeros preceding successive ones. The C scanner and A/F left sweep have exact costed run-list recurrences (Raw58LF1Sweep); repeated leading 001 blocks are factored as a separate counter (Raw58LF1Prefix and Raw58LF1Compressed). The arbitrary-list correctness lemmas and all three concrete evaluations were kernel-checked in Lean 4.36.0-rc2 against copied exact run0 and sweep definitions, using only standard axioms. Raw58LF1Late bridges them to original-source zipRead and zipCheck; targeted original-source audit pending. Since B1 is the sole hole, every nonhalting fill is total and never halts; the halting fill has the exact query count plus one. The normalization prefix has at most five moves. Thus the candidate LF1/parent bound must be at least 3055750, replacing 19310. This is below the canonical cutoff 6766859. The optional late-proof mapping for chunk_checks isolates the long-count leaves and checks exact table equality before using the compressed proof instead of reducing millions of raw steps. No complete LF1 or parent Cover is claimed.
