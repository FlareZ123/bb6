# Raw108: six-hole frontier cylinder

Parent `1RB---_1RC---_0RD---_1LD1RE_---1LB_------`; first query B1 at ordinary time 7. The root cut leaves 20 nontrivial children.

| B1 | Candidate weighted bound | Open leaves |
|---|---:|---:|
| 1LC | 97 | 83 |
| 0RD | 186 | 107 |
| 0LC | 108 | 165 |
| 1RC | 147 | 335 |
| 1RD | 111 | 667 |
| 0RE | 175 | 349 |
| 0LD | 197 | 573 |
| 1LA | 366 | 1030 |
| 1LB | 141 | 2369 |
| 1RF | 283 | 1521 |
| 0RC | 271 | 180 |
| 0RA | 377 | 460 |
| 1RA | 228 | 1011 |
| 1LF | 507 | 3067 |
| 1LE | 23598 | 4143 |

Complete candidate specifications in [specs.json](specs.json); original-source CI remains authoritative. New 1RA/228 passed [45610117731](https://github.com/FlareZ123/bb6/actions/runs/45610117731). The 1LF #1182 binary countdown, 1LE #768 paired-bit counter and #251 three-phase sweep passed copied-core local Lean. Full child audits for 1LF and 1LE are pending. 1LE #1651 reaches its first F0 hole at ordinary time 23597; the immediate-halt completion has candidate step count 23598. Thus the old 7014 cutoff is insufficient for a complete raw108 bound.

Five B1 children 0LA, 0LB, 0LE, 0LF, 0RF still need full specifications. The 0LE #1279/#1280 counter proofs passed original-source CI [45550931959](https://github.com/FlareZ123/bb6/actions/runs/45550931959). No timeout is a proof of nonhalting.

Reproduce with `generate.py <B1>` and manual `agent10-four-hole.yml` target `raw108-child`. Exact ordered open-list hashes and kernel-checked certificates are required. No universal raw108 theorem is claimed yet.
