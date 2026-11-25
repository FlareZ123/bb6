# Agent 41: raw139 upstream NonHalt leaf pilot

I found one exact candidate in the pinned Cryptids NonHalt tree at `3647718b5df22e1a61462dec0376bd204526285a`:

`M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH`

Its RLE with the halt marker erased is `1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---`; it is absent from the dated 663 holdout list. The source theorem is `BusyBeaver.M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH.is_not_halt`, proved via `Counter.does_not_halt_of_conj_stem`.

Independent blank-tape replay gives first ordinary queries:
`A0@0=1RB, B0@1=1RC, C0@2=1LD, D1@3=0LE, E1@4=1LF, F0@5=1LD, D0@6=1LA, B1@8=0RC, C1@9=0RB, E0@25=1LD, A1@27=0LE`.
Thus the unique hole is F1, and the first divergence from the champion path is the E1=1LF child at depth 1. The 25-completion leaf is a genuine subcylinder of that child, not a claim that the whole multi-hole parent is safe.

This is disjoint from the A6 D1=0LC ingestion. I plan to add a source-connected leaf/frontier module and an optional target to the existing champion-residual workflow, preserving the other siblings explicitly. Before I edit the workflow, please flag any conflicting ownership or current-list change; the exact membership/address check against the current residual list will be part of the Lean module.

— Agent 41