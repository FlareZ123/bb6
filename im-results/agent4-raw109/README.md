# Raw109 first-hole refinement

Parent `1RB---_1RC---_0RD---_1LD1RE_---1RB_------` (six holes, 25^6=244,140,625 completions) is raw residual 109 in canonical-121.json. The first unassigned query is B1 at ordinary step 7.

The full candidate census, using the established enumerate.cpp (1000-step search and 256-period cycle window), gives 12,444 split nodes, 225,927 side-cycle leaves, 48,981 last-hole leaves, 11,305 open leaves. Masses: 221,136,975 cycle; 18,386,481 halt; 1,175,544 total-defined; 3,441,625 open. Maximum observed weighted score 904. Applying the pooled bank from Agent1 raw60 gives 10,861 FAR candidates, with 444 initially unmatched. No cutoff is a verdict.

## Two complete candidate children

| B1 | Bound | Split | Cycle | Last-hole | FAR | Inductive |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 0LD | 324 | 595 | 11,100 | 2,266 | 316 | 4 |
| 0RE | 353 | 392 | 7,433 | 1,474 | 108 | 2 |

Six exact one-block sweep candidates (local open-list indices): 0LD 192,195,196,199 have entry 2, family C with head-inclusive left zipper 01(1111)^n1 and empty right zipper; growth times 29+24n,25+20n,25+16n,21+12n respectively. 0RE 0 has entry 8, E with left zipper 0011(1001)^n1; cost 29+14n. 0RE 1 has entry 3, D with left zipper 001(1011)^n1; cost 22+12n. Each returns to the same family at n+1. Symbolic arbitrary-tail block transfer discovery succeeded; proof generator emits finite rfl local steps, universal sweep inductions and never_of_growth. Original source audit pending.

Raw109Cut.lean also includes eleven immediate side-cycle children and the halt branch. If accepted, it proves parent dichotomy at 353, discharging 14 of 25 first-hole branches (136,718,750 raw completions) and retaining eleven (107,421,875). Retained B1 moves: 0LA,0LC,0LF,0RC,0RF,1LA,1LB,1LC,1LF,1RE,1RF.

Reproduction: python generate.py (reuses exact raw99 enumerator, raw107 bank, raw60 bank.txt, Agent31 sweep generator). specs.json pins candidate open-list SHA256s and counts. Then run existing agent10-four-hole.yml manual target raw109-cut, which compiles original-source dependency closure and rejects sorryAx/native_decide. The target was dispatched successfully. No BB(6) upper bound or complete raw109 decision is claimed.
