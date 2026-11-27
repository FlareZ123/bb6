# Raw139 E1=0RD, D0=1RF: complete computational candidate

The literal parent is `[7,24,11,24,14,24,23,16,24,13,24,24]`. An independent head-relative two-BigInt census at 140 ordinary transitions reports 29236 split nodes, 527600 translated cycles, 129371 last-hole leaves, 12846 small FAR leaves and 2612 additional tables. All additional tables now have candidate certificates: 2545 block-FAR recipes, 66 extended last queries and 1 translated cycle. Candidate weighted bound **8543**, with longest extended query at table index 944, primitive time 8537, slot 1. No exact source-accepted parent yet.

The initial width-two/three candidate pass left six tables. The decisive extra recipes, with parameters (width, cap, modulus, runs, reflection, phase), are:

| Index | Recipe |
| --- | --- |
| 25 | `[2,2,2,4,true,false]` |
| 326 | `[2,2,2,4,true,false]` |
| 570 | `[4,1,1,3,false,true]` |
| 571 | `[4,1,1,3,false,true]` |
| 1729 | `[2,2,2,4,false,false]` |
| 2190 | `[3,2,2,4,false,false]` |

The two width-four phase contexts (indices 570 and 571) close without any bounded-time assumption in the proposed finite-automata invariant. The untrusted graph saturation produced (33 left states, 130 right nodes, 248 events) and (86, 360, 769) respectively before minimization. This is a candidate nonhalting proof, not an accepted Lean theorem.

Reproduce using `discover-d0.js` and the original C++ replay at cutoff 140; reconcile ordered open array and exact counts against `census-d0rf1.json`. Reuse the existing original-source width-four specialization and bridge for the two width-four leaves, and the common width-two/three emitter for the others. No new search is needed. No global roster reduction or BB(6) value is claimed.
