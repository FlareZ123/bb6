# Raw120 E0=1LA: complete candidate certificate assignment

**Status:** candidate-complete discovery; original-source Lean integration is pending. This is a single child of raw120, not a parent closure or BB(6) value.

The raw parent is `1RB---_1RC---_0RD---_1LD1RE_1LA1LE_------`. The first-hole tree has 1,661 splits, 24,485 translated cycles, 9,483 last-hole leaves and 4,236 initially open leaves. The open-list SHA-256 is `90c10678c9a20c8583c13a390b319dc9aad3fa7f33730c3b019ec9fc9444929e`. Enumeration accounts for 9,765,625 completions, including halting choices.

Local discovery assigned 4,180 FAR candidates, 50 one-block and 3 two-block induction candidates, two late first-hole queries and one BiDFA certificate. All 4,236 open leaves have a proposed witness. The grouped-boundary search uses three same-state fresh-boundary observations to propose one or two repeat insertions, then tests an opaque-tail symbolic sweep and emits the existing inductive Lean proof format. The search is untrusted.

## Last hard leaf

Open index 1794: `1RB0LE_1RC0RF_0RD---_1LD1RE_1LA1LE_0RB1RA`. SAT synthesis gives left DFA `01234566212150`, right DFA `01231112`. A separate least fixed-point computation yields 43 abstract states and 10 left / 7 right admissible edges, with no C1 query. The explicit witness is in [Raw120OneLABiDFA.lean](Raw120OneLABiDFA.lean), using the source-linked Agent16 BiDFA checker. This finite closure is a candidate until Lean accepts it.

## Late queries

| Index | First hole | Primitive live steps |
|---|---|---:|
| 1943 | F0 | 13,107 |
| 1981 | F0 | 12,819 |

Both have only one unassigned slot. The candidate weighted bound is 13,113 (maximum query time plus six, as in the existing weighted checker). The two query traces are checked by the existing .last audit route; their nonhalting refinements require that route's last-hole hypotheses.

## Reproduce

Run `python im-results/agent3-tnf-raw120/generate_sibling.py 1LA` from the repository root. The existing manual coverage workflow target is `weighted-tnf-raw120-1la`. The generator refuses to claim a complete certificate if any leaf is unmatched. Full closure and axiom profiles must be accepted before this branch is promoted.
