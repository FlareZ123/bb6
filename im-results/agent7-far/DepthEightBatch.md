# Depth-eight residual FAR batch

Source roster pinned at `3f1d835463ff89764b83e59fb46ca0ffec568a5f`. Exhaustive canonical reachable left DFA enumeration of sizes 1–4 in both orientations; least NFA saturation and zero-suffix backward reachability. The 45 small-DFA certificates passed the full original-source closure in [run 45485309761](https://github.com/FlareZ123/bb6/actions/runs/45485309761), which rejects `sorryAx` and `native_decide`. Four already documented one-hole targets were omitted. No claim of whole-frontier closure.

| Leaf | Table | Tree path (slot index, move index) | DFA / reflected |
|---|---|---|---|
| leaf0 | `1RB---_1RC1LF_0RD0RC_1LD1RE_1LB0LB_0RC0LA` | tree114: [[8,6],[10,9]] | 1 / 1 |
| leaf1 | `1RB---_1RC1LF_0RD0RC_1LD1RE_0LC0LB_0RC0LA` | tree114: [[8,8],[10,9]] | 1 / 1 |
| leaf2 | `1RB---_1RC1LF_0RD0RC_1LD1RE_0LC0LB_0RD0LA` | tree114: [[8,8],[10,13]] | 1 / 1 |
| leaf3 | `1RB---_1RC1LF_0RD0RC_1LD1RE_0RC0LB_0RC0LA` | tree114: [[8,9],[10,9]] | 1 / 1 |
| leaf4 | `1RB---_1RC1LF_0RD0RC_1LD1RE_0RC0LB_0RD0LA` | tree114: [[8,9],[10,13]] | 1 / 1 |
| leaf5 | `1RB---_1RC1LF_0RD0RC_1LD1RE_0RC0LB_0LE0LA` | tree114: [[8,9],[10,16]] | 1 / 1 |
| leaf6 | `1RB---_1RC1LF_0RD0RC_1LD1RE_0RC0LB_1LE0LA` | tree114: [[8,9],[10,18]] | 1 / 1 |
| leaf7 | `1RB---_1RC1LF_0RD0RC_1LD1RE_1LC0LB_0RC0LA` | tree114: [[8,10],[10,9]] | 1 / 1 |
| leaf8 | `1RB---_1RC1LF_0RD0RC_1LD1RE_1LC0LB_0RD0LA` | tree114: [[8,10],[10,13]] | 1 / 1 |
| leaf9 | `1RB---_1RC1LF_0RD0RC_1LD1RE_1LD0LB_0RC0LA` | tree114: [[8,14],[10,9]] | 1 / 1 |
| leaf10 | `1RB---_1RC1LF_0RD1LC_1LD1RE_0RD0LB_0LB0LA` | tree115: [[10,4],[8,13]] | 1 / 1 |
| leaf11 | `1RB---_1RC1LF_0RD0LD_1LD1RE_0RB0LB_0LB0LA` | tree117: [[8,5],[10,4]] | 1 / 1 |
| leaf12 | `1RB---_1RC1LF_0RD0LD_1LD1RE_0RB0LB_1LD0LA` | tree117: [[8,5],[10,14]] | 1 / 1 |
| leaf13 | `1RB---_1RC1LF_0RD0LD_1LD1RE_0RC0LB_0RC0LA` | tree117: [[8,9],[10,9]] | 1 / 1 |
| leaf14 | `1RB---_1RC1LF_0RD0LE_1LD1RE_0RD0LB_0LB0LA` | tree121: [[10,4],[8,13]] | 1 / 1 |
| leaf15 | `1RB---_1RC1LF_0RD1LE_1LD1RE_0RD0LB_0LB0LA` | tree123: [[10,4],[8,13]] | 1 / 1 |
| leaf16 | `1RB1RF_1RC1LF_0RD1RB_1LD1RE_---0LB_1LD0LA` | tree112: [[1,23],[10,14]] | 2 / 0 |
| leaf17 | `1RB---_1RC1LF_0RD1LE_1LD1RE_0RD0LB_1RC0LA` | tree123: [[10,11],[8,13]] | 2 / 1 |
| leaf18 | `1RB1RD_1RC1LF_0RD0RF_1LD1RE_---0LB_0LA0LA` | tree126: [[10,0],[1,15]] | 2 / 0 |
| leaf19 | `1RB1LF_1RC1LF_0RD0RF_1LD1RE_---0LB_0LA0LA` | tree126: [[10,0],[1,22]] | 2 / 0 |
| leaf20 | `1RB1LF_1RC1LF_0RD0RF_1LD1RE_---0LB_1RA0LA` | tree126: [[10,3],[1,22]] | 2 / 0 |
| leaf21 | `1RB0RF_1RC1LF_0RD1RF_1LD1RE_---0LB_0RC0LA` | tree128: [[10,9],[1,21]] | 2 / 0 |
| leaf22 | `1RB1RD_1RC1LF_0RD1RF_1LD1RE_---0LB_1RC0LA` | tree128: [[10,11],[1,15]] | 2 / 0 |
| leaf23 | `1RB1LF_1RC1LF_0RD1RF_1LD1RE_---0LB_1RC0LA` | tree128: [[10,11],[1,22]] | 2 / 0 |
| leaf24 | `1RB---_1RC1LF_0RD1LC_1LD1RE_0RC0LB_0LB0LA` | tree115: [[10,4],[8,9]] | 3 / 1 |
| leaf25 | `1RB1RF_1RC1LF_0RD1LE_1LD1RE_---0LB_0RA0LA` | tree123: [[10,1],[1,23]] | 3 / 0 |
| leaf26 | `1RB0LC_1RC1LF_0RD0RF_1LD1RE_---0LB_1RA0LA` | tree126: [[10,3],[1,8]] | 3 / 0 |
| leaf27 | `1RB1RD_1RC1LF_0RD0RF_1LD1RE_---0LB_1RA0LA` | tree126: [[10,3],[1,15]] | 3 / 0 |
| leaf28 | `1RB0RF_1RC1LF_0RD1RA_1LD1RE_---0LB_0LD0LA` | tree86: [[1,21],[10,12]] | 4 / 0 |
| leaf29 | `1RB0LD_1RC1LF_0RD1RB_1LD1RE_1LC0LB_---0LA` | tree112: [[1,12],[8,10]] | 4 / 0 |
| leaf30 | `1RB0LD_1RC1LF_0RD1RB_1LD1RE_1RD0LB_---0LA` | tree112: [[1,12],[8,15]] | 4 / 0 |
| leaf31 | `1RB0LD_1RC1LF_0RD1RB_1LD1RE_1LF0LB_---0LA` | tree112: [[1,12],[8,22]] | 4 / 0 |
| leaf32 | `1RB1RE_1RC1LF_0RD1RB_1LD1RE_1LA0LB_---0LA` | tree112: [[1,19],[8,2]] | 4 / 0 |
| leaf33 | `1RB1RE_1RC1LF_0RD1RB_1LD1RE_0LB0LB_---0LA` | tree112: [[1,19],[8,4]] | 4 / 0 |
| leaf34 | `1RB1RE_1RC1LF_0RD1RB_1LD1RE_1LD0LB_---0LA` | tree112: [[1,19],[8,14]] | 4 / 0 |
| leaf35 | `1RB1RF_1RC1LF_0RD1RB_1LD1RE_---0LB_0LB0LA` | tree112: [[1,23],[10,4]] | 4 / 0 |
| leaf36 | `1RB1RE_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA` | tree116: [[8,22],[1,19]] | 4 / 0 |
| leaf37 | `1RB1RD_1RC1LF_0RD0LD_1LD1RE_1RB0LB_---0LA` | tree117: [[8,7],[1,15]] | 4 / 0 |
| leaf38 | `1RB1LF_1RC1LF_0RD0LD_1LD1RE_1RB0LB_---0LA` | tree117: [[8,7],[1,22]] | 4 / 0 |
| leaf39 | `1RB---_1RC1LF_0RD0RE_1LD1RE_0RC0LB_0LC0LA` | tree122: [[8,9],[10,8]] | 4 / 1 |
| leaf40 | `1RB0LC_1RC1LF_0RD1RE_1LD1RE_1RD0LB_---0LA` | tree124: [[8,15],[1,8]] | 4 / 0 |
| leaf41 | `1RB0LD_1RC1LF_0RD1RE_1LD1RE_1RD0LB_---0LA` | tree124: [[8,15],[1,12]] | 4 / 0 |
| leaf42 | `1RB---_1RC1LF_0RD0RF_1LD1RE_0LC0LB_0RD0LA` | tree126: [[10,13],[8,8]] | 4 / 1 |
| leaf43 | `1RB1RF_1RC1LF_0RD0RF_1LD1RE_---0LB_1LF0LA` | tree126: [[10,22],[1,23]] | 4 / 0 |
| leaf44 | `1RB1LD_1RC1LF_0RD1RF_1LD1RE_---0LB_1RB0LA` | tree128: [[10,7],[1,14]] | 4 / 0 |

Total additional accepted certificates: 45; exact trial count 103357. Original-source Lean acceptance complete for these 45. The tree integration and overlap with newer certificates must be checked before decrementing any shared frontier count.

## Additional size-five to size-nine certificates

The local C++ `roster_far.cpp` search used the 52 remaining tables after the four prior and 45 small-DFA hits: exhaustive canonical d=5 enumeration and 30,000 guided mutations per larger size (6–10), both orientations, seed `0xB66F123`, command `roster_far remaining-roster.txt 0 1 30000 10`. It returned 42 candidates; the displayed DFA arrays are enough to reconstruct the least saturated masks independently. Source acceptance is pending.

| Leaf | Table | Tree path (slot index, move index) | DFA / reflected |
|---|---|---|---|
| leaf1 | `1RB1RD_1RC1LF_0RD1LA_1LD1RE_1RC0LB_---0LA` | tree85: [[1,15],[8,11]] | 5 / 0 |
| leaf2 | `1RB1RD_1RC1LF_0RD1LA_1LD1RE_1RD0LB_---0LA` | tree85: [[1,15],[8,15]] | 5 / 0 |
| leaf3 | `1RB0LD_1RC1LF_0RD1RA_1LD1RE_0LB0LB_---0LA` | tree86: [[1,12],[8,4]] | 5 / 0 |
| leaf4 | `1RB0LD_1RC1LF_0RD1RA_1LD1RE_1LD0LB_---0LA` | tree86: [[1,12],[8,14]] | 5 / 0 |
| leaf5 | `1RB0RE_1RC1LF_0RD1RA_1LD1RE_0LD0LB_---0LA` | tree86: [[1,17],[8,12]] | 5 / 0 |
| leaf6 | `1RB1RE_1RC1LF_0RD1RA_1LD1RE_0LE0LB_---0LA` | tree86: [[1,19],[8,16]] | 6 / 0 |
| leaf8 | `1RB1RF_1RC1LF_0RD1RA_1LD1RE_---0LB_0LE0LA` | tree86: [[1,23],[10,16]] | 7 / 0 |
| leaf9 | `1RB0LC_1RC1LF_0RD1RB_1LD1RE_0LA0LB_---0LA` | tree112: [[1,8],[8,0]] | 5 / 0 |
| leaf10 | `1RB0LC_1RC1LF_0RD1RB_1LD1RE_1RA0LB_---0LA` | tree112: [[1,8],[8,3]] | 5 / 0 |
| leaf11 | `1RB0LC_1RC1LF_0RD1RB_1LD1RE_1RB0LB_---0LA` | tree112: [[1,8],[8,7]] | 5 / 0 |
| leaf12 | `1RB0LC_1RC1LF_0RD1RB_1LD1RE_0RF0LB_---0LA` | tree112: [[1,8],[8,21]] | 5 / 0 |
| leaf13 | `1RB0LD_1RC1LF_0RD1RB_1LD1RE_1LE0LB_---0LA` | tree112: [[1,12],[8,18]] | 6 / 0 |
| leaf14 | `1RB0LD_1RC1LF_0RD0RC_1LD1RE_1RB0LB_---0LA` | tree114: [[8,7],[1,12]] | 6 / 0 |
| leaf19 | `1RB1LA_1RC1LF_0RD1RC_1LD1RE_0LF0LB_---0LA` | tree116: [[8,20],[1,2]] | 6 / 0 |
| leaf20 | `1RB1LA_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA` | tree116: [[8,22],[1,2]] | 6 / 0 |
| leaf21 | `1RB0LD_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA` | tree116: [[8,22],[1,12]] | 6 / 0 |
| leaf25 | `1RB0LB_1RC1LF_0RD0LD_1LD1RE_1RA0LB_---0LA` | tree117: [[8,3],[1,4]] | 5 / 0 |
| leaf26 | `1RB1LD_1RC1LF_0RD0LD_1LD1RE_1RA0LB_---0LA` | tree117: [[8,3],[1,14]] | 5 / 0 |
| leaf27 | `1RB1LE_1RC1LF_0RD0LD_1LD1RE_1RB0LB_---0LA` | tree117: [[8,7],[1,18]] | 8 / 0 |
| leaf28 | `1RB0LC_1RC1LF_0RD0RE_1LD1RE_0LA0LB_---0LA` | tree122: [[8,0],[1,8]] | 5 / 0 |
| leaf29 | `1RB1RD_1RC1LF_0RD0RE_1LD1RE_0LA0LB_---0LA` | tree122: [[8,0],[1,15]] | 5 / 0 |
| leaf30 | `1RB1LE_1RC1LF_0RD0RE_1LD1RE_0LA0LB_---0LA` | tree122: [[8,0],[1,18]] | 5 / 1 |
| leaf31 | `1RB1LF_1RC1LF_0RD0RE_1LD1RE_0LA0LB_---0LA` | tree122: [[8,0],[1,22]] | 5 / 0 |
| leaf32 | `1RB0LC_1RC1LF_0RD0RE_1LD1RE_1RA0LB_---0LA` | tree122: [[8,3],[1,8]] | 7 / 0 |
| leaf33 | `1RB---_1RC1LF_0RD0RE_1LD1RE_0RB0LB_0LD0LA` | tree122: [[8,5],[10,12]] | 5 / 0 |
| leaf34 | `1RB---_1RC1LF_0RD0RE_1LD1RE_1RC0LB_0LB0LA` | tree122: [[8,11],[10,4]] | 5 / 0 |
| leaf35 | `1RB---_1RC1LF_0RD0RE_1LD1RE_1RC0LB_1LD0LA` | tree122: [[8,11],[10,14]] | 5 / 0 |
| leaf36 | `1RB---_1RC1LF_0RD1RE_1LD1RE_0RB0LB_0LE0LA` | tree124: [[8,5],[10,16]] | 8 / 0 |
| leaf37 | `1RB0LB_1RC1LF_0RD1RE_1LD1RE_1RB0LB_---0LA` | tree124: [[8,7],[1,4]] | 5 / 0 |
| leaf38 | `1RB1LC_1RC1LF_0RD1RE_1LD1RE_1RB0LB_---0LA` | tree124: [[8,7],[1,10]] | 5 / 0 |
| leaf39 | `1RB1LD_1RC1LF_0RD1RE_1LD1RE_1RB0LB_---0LA` | tree124: [[8,7],[1,14]] | 5 / 0 |
| leaf40 | `1RB1RD_1RC1LF_0RD1RE_1LD1RE_1RC0LB_---0LA` | tree124: [[8,11],[1,15]] | 5 / 0 |
| leaf41 | `1RB1LE_1RC1LF_0RD1RE_1LD1RE_1RC0LB_---0LA` | tree124: [[8,11],[1,18]] | 7 / 0 |
| leaf42 | `1RB1LF_1RC1LF_0RD1RE_1LD1RE_1RC0LB_---0LA` | tree124: [[8,11],[1,22]] | 5 / 0 |
| leaf43 | `1RB1RD_1RC1LF_0RD1RE_1LD1RE_1RD0LB_---0LA` | tree124: [[8,15],[1,15]] | 5 / 0 |
| leaf44 | `1RB1LF_1RC1LF_0RD1RE_1LD1RE_1RD0LB_---0LA` | tree124: [[8,15],[1,22]] | 5 / 0 |
| leaf45 | `1RB0RD_1RC1LF_0RD1RE_1LD1RE_0RF0LB_---0LA` | tree124: [[8,21],[1,13]] | 5 / 0 |
| leaf47 | `1RB1LE_1RC1LF_0RD0RF_1LD1RE_---0LB_0LA0LA` | tree126: [[10,0],[1,18]] | 9 / 0 |
| leaf48 | `1RB0RF_1RC1LF_0RD0RF_1LD1RE_---0LB_1LA0LA` | tree126: [[10,2],[1,21]] | 5 / 0 |
| leaf49 | `1RB0RD_1RC1LF_0RD0RF_1LD1RE_---0LB_1LB0LA` | tree126: [[10,6],[1,13]] | 5 / 0 |
| leaf51 | `1RB1LE_1RC1LF_0RD1RF_1LD1RE_---0LB_1RC0LA` | tree128: [[10,11],[1,18]] | 7 / 0 |
| leaf52 | `1RB0RD_1RC1LF_0RD1RF_1LD1RE_---0LB_0RF0LA` | tree128: [[10,21],[1,13]] | 5 / 0 |

## Ten remaining tables from the pinned 101-leaf roster

These have no certificate from the above search; their halt status is unknown. No inference about larger DFA sizes is justified.

| Table | Tree path |
|---|---|
| `1RB0RF_1RC1LF_0RD1RA_1LD1RE_---0LB_1LA0LA` | tree86: [[1,21],[10,2]] |
| `1RB---_1RC1LF_0RD1LC_1LD1RE_1RC0LB_0RF0LA` | tree115: [[10,21],[8,11]] |
| `1RB---_1RC1LF_0RD1LC_1LD1RE_0RE0LB_0RF0LA` | tree115: [[10,21],[8,17]] |
| `1RB1LA_1RC1LF_0RD1RC_1LD1RE_1RB0LB_---0LA` | tree116: [[8,7],[1,2]] |
| `1RB1LA_1RC1LF_0RD1RC_1LD1RE_0LE0LB_---0LA` | tree116: [[8,16],[1,2]] |
| `1RB1RD_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA` | tree116: [[8,22],[1,15]] |
| `1RB1LE_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA` | tree116: [[8,22],[1,18]] |
| `1RB1LF_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA` | tree116: [[8,22],[1,22]] |
| `1RB0RB_1RC1LF_0RD0LF_1LD1RE_---0LB_0RF0LA` | tree125: [[1,5],[10,21]] |
| `1RB1RF_1RC1LF_0RD0RF_1LD1RE_---0LB_0RE0LA` | tree126: [[10,17],[1,23]] |

## Warm-started automata search on the final ten

The local `large_far.cpp` search (128-bit masks, warm starts from sibling certificates, scored mutations and state splitting, 50,000 trials per nominal size 5–16 and orientation, seed 123) found nine more candidates. Independent BigInt saturation reproduced all nine. The single remaining target is `1RB1RF_1RC1LF_0RD0RF_1LD1RE_---0LB_0RE0LA` at tree126 path `[[10,17],[1,23]]`. These are pending original-source acceptance.

| Leaf | Table | Tree path | DFA / reflected |
|---|---|---|---|
| leaf1 | `1RB0RF_1RC1LF_0RD1RA_1LD1RE_---0LB_1LA0LA` | tree86: [[1,21],[10,2]] | 8 / 0 |
| leaf2 | `1RB---_1RC1LF_0RD1LC_1LD1RE_1RC0LB_0RF0LA` | tree115: [[10,21],[8,11]] | 7 / 0 |
| leaf3 | `1RB---_1RC1LF_0RD1LC_1LD1RE_0RE0LB_0RF0LA` | tree115: [[10,21],[8,17]] | 9 / 0 |
| leaf4 | `1RB1LA_1RC1LF_0RD1RC_1LD1RE_1RB0LB_---0LA` | tree116: [[8,7],[1,2]] | 7 / 1 |
| leaf5 | `1RB1LA_1RC1LF_0RD1RC_1LD1RE_0LE0LB_---0LA` | tree116: [[8,16],[1,2]] | 8 / 0 |
| leaf6 | `1RB1RD_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA` | tree116: [[8,22],[1,15]] | 12 / 1 |
| leaf7 | `1RB1LE_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA` | tree116: [[8,22],[1,18]] | 7 / 0 |
| leaf8 | `1RB1LF_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA` | tree116: [[8,22],[1,22]] | 12 / 0 |
| leaf9 | `1RB0RB_1RC1LF_0RD0LF_1LD1RE_---0LB_0RF0LA` | tree125: [[1,5],[10,21]] | 11 / 0 |
