# Raw11 extra126: all fourteen open leaves have exact unary-sweep recurrences

The retained tree for Raw11 extra parent 126 has 7,989 nodes, candidate weighted bound 167, and fourteen open leaves. The search partition comprises 5,048 side, 1,008 automata, 1,570 last-hole, 333 split, 16 FAR and 14 open leaves. All fourteen are decided in the centered infinite-tape model by the same three-stage proof: right triple transfer, finite right turn, left pair transfer and finite finish.

The section S(x) is E1 with exactly two ones to its left and x ones to its right, with zero padding. Every variant reaches S(1) after eleven transitions. Let x=6n+r. For the finite rule parameters (a,T,F,r,s) in the source, the return costs (2a+6)n+T+F and ends at S(6n+s). Right triple transfers take a=5 except variants 6 (a=7) and 7 (a=3). The B1/D1 left sweep preserves every one. Finite turn and finish identities hold for arbitrary surrounding tails; the unbounded sweeps follow by induction.

| Variant | Exact table | Section itinerary (offsets relative to 6n) |
|---|---|---|
| 0 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_---0RF_1LA0LA` | 1 → 3 → 7 |
| 1 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_---0RF_0RB0LA` | 1 → 3 → 9 |
| 2 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_---0RF_0LC0LA` | 1 → 3 → 6 → 7 |
| 3 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_---0RF_1LC0LA` | 1 → 3 → 7 |
| 4 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_---0RF_0LD0LA` | 1 → 3 → 6 → 7 |
| 5 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_---0RF_1LD0LA` | 1 → 3 → 7 |
| 6 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_0RD1RF_---0LC` | 1 → 5 → 8 → 13 |
| 7 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_---1RF_0RB1RC` | 1 → 3 → 7 |
| 8 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_0LA1RF_---0RD` | 1 → 5 → 7 |
| 9 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_0RA1RF_---0RD` | 1 → 5 → 13 |
| 10 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_1LA1RF_---0RD` | 1 → 5 → 7 |
| 11 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_1LB1RF_---0RD` | 1 → 5 → 7 |
| 12 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_0RD1RF_---0RD` | 1 → 5 → 8 → 13 |
| 13 | `1RB1RD_1RC1LD_0LA1RE_1LA1LB_1LE1RF_---0RD` | 1 → 5 → 8 → 13 |

Variant 1 enters its steady residue-3 cycle at time 26. Every other itinerary closes its starting residue with a positive increment of six or twelve. All cycles take positive time, so successful blank runs have unbounded length; the undefined transition cannot occur.

[Raw11Extra126.lean](Raw11Extra126.lean) defines these exact partial tables and proves all 33 residue return identities and the uniform theorem `Raw11Extra126.never (v : Fin 14) (n : Nat)`. Local Lean 4.36.0-rc2 accepted the centered-model source using the exact required definitions sliced from Root56.lean, and both returnRule and never depend only on propext and Quot.sound. No sorry or native_decide. The repository copy is reconstructed from the locally checked generator; the exact repository dependency closure and weighted-model bridge are not yet compiler checked. This does not yet establish a weighted parent Cover.

Next: prove the exact centered-to-WeightedTNF transfer (use the same Root56Coverage center/applyMove bridge), consume all 14 exact leaves in the retained parent126 search tree, then integrate the parent only after full kernel audit. Parent137's sole open leaf has a separate recurrence (raw11-extra-137.md). Thus all 15 open leaves of the two parents are mathematically decided in the centered model; neither parent is yet claimed covered.
