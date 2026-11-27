# Exact residual exceptions to the broad E0=0LC search

Codes are 4*destination + 2*write + direction (R=1); 24 is an unassigned row. Table order A0,A1,...,F1. Candidate witnesses, not yet all kernel accepted. Recipes block/phase/mirror/mirrorphase have width, cap, mod, runs. Offset additionally has initial position. Cycle has entry, period, direction, boundary. Late has query step and slot. For this parent the full six states are available at the first D0 hole or introduced canonically by its assignment.

| D0 | Index | Exact table | Recipe |
|---|---:|---|---|
| 0LA | 529 | 7,22,11,24,14,9,0,16,8,11,4,14 | cycle 7679 740 false -68 |
| 0LA | 530 | 7,22,11,24,14,9,0,16,8,11,6,14 | late 80371 3 |
| 0LA | 718 | 7,24,11,23,14,21,0,16,8,11,5,16 | late 4028 1 |
| 0LA | 840 | 7,1,11,24,14,22,0,16,8,11,23,3 | late 16947 3 |
| 0LA | 881 | 7,4,11,24,14,22,0,16,8,11,13,21 | offset 3 2 2 6 0 |
| 0LF | 368 | 7,24,11,7,14,21,20,16,8,11,2,21 | mirrorphase 3 1 5 4 |
| 0LF | 737 | 7,24,11,23,14,7,20,16,8,11,3,21 | mirrorphase 2 1 5 4 |
| 0RA | 468 | 7,13,11,21,14,3,1,16,8,11,24,7 | late 3832 10 |
| 0RA | 477 | 7,13,11,21,14,3,1,16,8,11,24,12 | late 3940 10 |
| 0RA | 630 | 7,15,11,21,14,0,1,16,8,11,24,3 | offset 4 1 3 6 0 |
| 0RF | 1253 | 7,24,11,13,14,10,21,16,8,11,3,23 | late 2410 1 |
| 1LA | 528 | 7,19,11,21,14,1,2,16,8,11,24,11 | mirror 2 1 2 2 |
| 1LA | 751 | 7,19,11,23,14,1,2,16,8,11,24,5 | mirrorphase 2 1 7 4 |
| 1LA | 724 | 7,10,11,23,14,9,2,16,8,11,24,3 | mirrorphase 2 1 7 4 |
| 1LA | 825 | 7,24,11,23,14,7,2,16,8,11,3,21 | mirrorphase 2 1 5 4 |
| 1LA | 835 | 7,24,11,23,14,5,2,16,8,11,6,21 | mirror 3 1 2 4 |
| 1LB | 20 | 7,1,11,21,14,1,6,16,8,11,24,19 | mirror 3 1 4 4 |
| 1LB | 61 | 7,19,11,21,14,1,6,16,8,11,24,19 | mirror 3 1 4 4 |
| 1LB | 74 | 7,19,11,23,14,1,6,16,8,11,24,10 | mirror 3 1 4 4 |
| 1LB | 227 | 7,22,11,24,14,3,6,16,8,11,21,1 | mirror 3 1 3 4 |
| 1LB | 230 | 7,22,11,24,14,3,6,16,8,11,7,21 | mirror 3 1 3 4 |
| 1LB | 439 | 7,10,11,24,14,21,6,16,8,11,0,3 | late 2509 3 |
| 1LB | 545 | 7,1,11,24,14,22,6,16,8,11,23,3 | late 4655 3 |
| 1LB | 622 | 7,1,11,24,14,23,6,16,8,11,7,2 | mirror 3 1 3 4 |
| 1RA | 166 | 7,3,11,24,14,21,3,16,8,11,11,17 | offset 3 1 5 6 0 |
| 1RA | 169 | 7,3,11,24,14,21,3,16,8,11,15,17 | offset 4 1 7 6 1 |
| 1RB | 253 | 7,24,11,3,14,21,7,16,8,11,11,17 | offset 3 1 5 6 0 |
| 1RC | 189 | 7,21,11,24,14,3,11,16,8,11,11,17 | late 16067 3 |
| 1RF | 424 | 7,10,11,24,14,21,23,16,8,11,16,3 | mirror 2 1 4 4 |

Two late multi-hole cases: 0LA312 = [7,22,11,24,14,3,0,16,8,11,24,9], B1 at561; 1RF255 = [7,17,11,24,14,1,23,16,8,11,24,3], B1 at258. Expand B1 to halt and all 24 ordinary moves. Use search_case on each ordinary child. All pass except 0LA312/B1=0RC (code9), which passes normal block width3 cap1 mod3 runs5 (83 left,161 right). Independently mirrorphase width2 cap1 mod5 runs4 also succeeds.

Candidate longest ordinary query 80371; proposed weighted bound 80377. Packed replays for 718 and 840 are already kernel checked. The 29 exceptions plus two late multi-hole expansions close all 13,323 initially unclassified leaves of the twelve broad D0 branches at the search/recipe layer; the current emitter supports block, phase, mirror, mirrorphase and offset recipes. The complete E0=0LC parent combines those twelve broad Covers with eleven direct cycle children and the exact locally kernel-checked D0=0RC Cover at weighted bound 616 (the older bound-775 artifact has E0=0LD and is inapplicable). The full parent theorem at bound 80377 remains pending Lean 4.36.0-rc2 CI; candidate classification is not a kernel-checked parent proof.
