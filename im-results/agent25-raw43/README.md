# Raw43: five-hole child bounds

Parent: `1RB---_1RC---_0RD---_1LD0RB_------_------` (seven holes). Its first missing transition is B1. The following two children fix B1=0RE and E1 as indicated. The complete parent requires all other branches too.

| E1 | Candidate weighted bound | Side cycles | Last holes | Split nodes | Remaining certificates |
| --- | ---: | ---: | ---: | ---: | --- |
| 0LE | 75 | 5371 | 995 | 279 | 51 FAR, 1 universal growth |
| 0RD | 49 | 2878 | 273 | 137 | 1 FAR |

Each child has 25^5 = 9,765,625 raw completions. Neither complete child is claimed source-accepted in this note. No parent or canonical roster deletion follows until the full original-source checks and composition pass.

## New 0RD child: complete finite certificate candidate

For `1RB---_1RC0RE_0RD---_1LD0RB_---0RD_------`, the exact-trace candidate enumeration (1000-step discovery cap, lookback 32) gives 9,271,750 completions in translated-cycle leaves, 493,850 in bounded-query/total-table leaves, and 25 in the single remaining partial table `1RB0LF_1RC0RE_0RD---_1LD0RB_1RF0RD_1LA0RE`. The maximum missing-transition query time is 43, so the weighted cutoff candidate is 49 (one halting step plus at most five first-one delay steps).

The remaining table admits a one-state FAR witness with orientation 0, delta [0,0], left masks [2,4,8,26,32,16,64], right masks [32,16,64,2,8,16,64], and blank-zero closure mask 64. Every FAR closure implication is satisfied and the start bit is absent. This covers all 25 C1 completions, not merely the all-nonhalt choice. The census was computed in JavaScript using 32-bit rolling hashes solely for candidate selection and direct versioned-tape comparison for side equality. The existing C++ 64-bit generator is the independent reproducibility route; the new spec checks the exact open roster, root query, and tree census before emitting Lean certificates.

Run `python im-results/agent25-raw43/generate.py 0rd` after preparing the existing shared source. The generated theorem is `BB6.Agent25Raw43RD.all43child`, with exact target `WeightedBound 49`. Use existing workflow agent10-four-hole.yml target raw43-0rd. Local shell and Python failed at the tool boundary (ClientError, before any command execution); no local Lean compilation or C++ replay was possible this invocation. The generated theorem is a draft until a successful original-source compiler and axiom audit.

## Prior 0LE child

Candidate enumeration: 9,237,475 cycle completions, 525,050 bounded-query/total-table completions, and 3,100 open completions. The spec supplies FAR witnesses for 51 leaves. For the last partial table M29, `1RB0RF_1RC0RE_0RD0RA_1LD0RB_1LF0LE_1LB---`, define S(n) = (A, [1,0,1], (01)^n 0) in the left-includes-scanned-cell zipper convention. Blank reaches S(1) after 16 steps. Two arbitrary-tail sweeps, a right turn and left turn give S(n) -> S(n+3) in exactly 8n+28 steps. Hence S(3k+1) grows forever, never querying F1. Entry and growth equalities were locally Lean-checked against copied zipper definitions in the prior invocation; original-source adapter and complete child audit not established here.

## Parent strategy

E/F relabeling fixes the parent and the blank start. The already existing weighted symmetry transport can mirror B1=0RE into B1=0RF (E1 becomes F1), avoiding duplicate certification of these two isomorphic branches. The E/F-fixed branches and remaining E1 choices still need actual certificates. Do not infer full Raw43 closure from these two children.
