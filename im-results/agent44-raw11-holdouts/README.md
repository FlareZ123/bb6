# Source-level finite-hole certificates for the frozen Raw11 six-hole frontier

From Agent5's run 45896597080, omit Extra134 (already accepted) and inspect only the 111 unresolved leaf tables. Primitive simulation found 28 last-hole reaches within 1,000,000 transitions. Three are now locally Lean-kernel checked on the original FastPhaseTree/PackedZipper source checker (Lean 4.36.0-rc2, core artifact 15271118488); the respective parents each had exactly one unresolved leaf in the frozen scan.

| Extra ID | Leaf table | Ordinary steps | Weighted bound |
|---:|---|---:|---:|
| 48 | `1RB1LB_1RC0LB_0LA0LD_1LB1RE_0RF---_1RD1LB` | 4869 | 4875 |
| 59 | `1RB1LB_1RC1LB_0LA1RD_1LE0RC_---0LF_1RD0LD` | 2484 | 2490 |
| 66 | `1RB1LB_1RC1LC_0LA1LD_0LF1RE_1RA0RE_0LA---` | 2430 | 2436 |

Each `Agent44Extra<ID>Hole00.cover` was compiled locally, with axioms [propext, Classical.choice, Quot.sound], using `by decide +kernel` and packed step joins. These results classify exact leaves, not entire parent trees. The previous parent tree must be replayed with its other certificates and this leaf proof before consuming any parent from Raw11. No global frontier decrement is claimed. Extra13 and Extra14 also reach their last hole at 15937 and 20790 steps respectively (kernel proofs pending); Extra47 reaches its hole at 719358 steps (computational only). Do not rerun the original discovery for already classified leaves.
