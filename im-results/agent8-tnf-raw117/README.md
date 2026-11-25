# Six-hole raw117 and raw112 candidate classification

Raw117 is the six-hole sibling E1=1RD, parent `1RB---_1RC---_0RD---_1LD1RE_---1RD_------`. Raw112 differs only at E1=1LC. Each has exactly 25^6 = 244,140,625 compatible full tables.

| raw | splits | side cycles | last holes | open leaves | FAR | symbolic | late query | still open |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 117 | 7903 | 143850 | 32350 | 5570 | 5530 | 39 | 1 | 0 |
| 112 | 25004 | 446232 | 115572 | 13289 | 12896 | 0 | 0 | 393 |

Raw117 is now a complete **candidate** closure at weighted score 1291. The original discovery cutoff 1000 missed leaf 2707, whose sole unassigned F0 is queried at ordinary time 1290. All fixed zero-writing rows fail to enter A; weighted delay is zero. The initial score 235 is superseded. The exact open-list hash and leaf index set are pinned by discover.py. Raw112 candidate maximum 980 remains provisional.

The 39 symbolic candidates comprise 30 one-block, four two-block, two extended returns, and the three nested-growth leaves. [Raw117Nested.lean](Raw117Nested.lean) proves both 4215 (A1=1LE) and 4216 (A1=1LF). Writing A(L,m,k) for zipper left word L and right word 1^m 0001 0^k 1, d=3 or 2 respectively, m(p)=d(p+1)+1, the exact universal return changes a scanned zero into one, preserves its arbitrary left tail, leaves m(p) fixed and changes k to k+2^p. Strong induction with an inner finite stack traversal proves this for every p,k. After the 31/30-step blank entry, the family A([],m(p),2^p-1) returns to its p+1 member in strictly positive time. No sampled recurrence is assumed.

[Raw117Quadratic.lean](Raw117Quadratic.lean) proves leaf 397. B(l,m,k) has right word 1^m (01)^k 0. Its exact even/odd returns reduce the unary length by four per pair and increment the alternating count; the remaining alternating word is consumed and a final sweep yields B([],4(n+1)+2,1) from B([],4n+2,1). Blank entry is at step 13. The two hard proof modules' macro equations, universal inductions, growth and cost selections compiled locally in Lean 4.36.0-rc2 against exact copied executable Z0, move0, step0, run0 and join0 definitions; the growth theorem axioms are propext and Quot.sound. Their final source NeverHalts bridges and complete weighted tree remain pending source CI.

## Reproduction

`python im-results/agent8-tnf-raw117/discover.py 117 --sweeps` or `112` regenerates candidate data. `generate.py` emits the source-linked Raw117Data audit with exact attaining witness and theorem exact117. It reuses ZipThreeHoleAudit, checks every branch, and never treats the time cutoff as proof. Source CI must pass before removing raw117 from the canonical roster or claiming its exact weighted maximum as a certified theorem. No BB(6) upper bound follows yet.
