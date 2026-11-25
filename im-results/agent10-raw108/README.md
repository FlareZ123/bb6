# Raw108: six-hole frontier cylinder

Parent `1RB---_1RC---_0RD---_1LD1RE_---1LB_------`; first query B1 at ordinary time 7. The root cut leaves 20 nontrivial children. The complete candidate specifications currently cover 19 children; **the unconditional parent bound is not established**. The candidate bound must accommodate long halters beyond the early 7014 cutoff, especially 0LE (192168).

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
| 0LE | 192168 | 2251 |
| 0LF | 1235 | 2784 |
| 0RF | 288 | 602 |
| 0LA | 26340 | 1956 |

The already accepted original-source audits include 0RD/186 ([45534584949](https://github.com/FlareZ123/bb6/actions/runs/45534584949)), 0LC/108 ([45534857294](https://github.com/FlareZ123/bb6/actions/runs/45534857294)), 1RC/147 ([45535246195](https://github.com/FlareZ123/bb6/actions/runs/45535246195)), 1RD/111 ([45535435037](https://github.com/FlareZ123/bb6/actions/runs/45535435037)), and 1RA/228 ([45610117731](https://github.com/FlareZ123/bb6/actions/runs/45610117731)). The 0LE #1279/#1280 counter proofs passed [45550931959](https://github.com/FlareZ123/bb6/actions/runs/45550931959). Other full-child status must be verified before parent composition.

## 0RF: completed candidate certificate at weighted 288

The 602-leaf open roster (exact digest in [specs.json](specs.json)) has 586 FAR witnesses, 14 automatic positive-return witnesses, and two arbitrary-word grammar witnesses. In particular, the last non-FAR leaf #411 (`1RB1LA_1RC0RF_0RD0RC_1LD1RE_---1LB_0LA1LF`) has an exact inductive family at C, using the left list including the scanned cell:

```
C(1110000001111100000 (111000)^n 11111000111, 1^(53+18n))
  -- 1820+432n ordinary steps -->
C(1110000001111100000 (111000)^(n+1) 11111000111, 1^(53+18(n+1)))
```

The entry occurs at step 2862. All 14 automatic entry/growth proofs, including #411, passed local Lean 4.36.0-rc2 with the copied exact zipper/sweep core. The #62 and #115 arbitrary-word grammar proofs also passed locally, as did the separate 0LF #854 two-language grammar. Original-source compilation of the new 0RF child and final `NeverHalts` adapters is still required. No unresolved leaf is classified by a timeout.

## 0LA: complete candidate partition (source audit pending)

The ordered census of 1,956 open leaves is pinned by its SHA-256 digest in [specs.json](specs.json). The final specification uses a 76-code FAR bank, 128 symbolic positive-return witnesses, ten translated-cycle witnesses, four delayed first-hole queries, three prior manual counter proofs, and a width-six block-FAR witness for #114. The last candidate block saturation has 122 left states, 479 right nodes and 857 edges before minimization. Leaf #1099 has a 13-state ordinary FAR witness. Leaf #14 reaches its sole hole E0 after 26,334 transitions, so the candidate bound is raised to 26,340. Leaf #69 returns in 1026+756n steps, adding three copies of 00111011 to its retained list. These are candidate-level results until the original-source checker accepts the generated `all_completions` theorem.

## Remaining obligations

The remaining missing child specification is 0LB. For each completed child, the original-source `all_completions` theorem must be accepted. Integrate those weighted bounds with the root cut and the mixed-score canonical quotient; lift the small-cutoff branches to the maximum actual certified child bound (at least 192168 from current candidates) or the attained champion score B.

Reproduce with `python generate.py <B1>` and manual `agent10-four-hole.yml` target `raw108-child`. The checker reconstructs the exact ordered census, replays each sweep, and checks the FAR masks and all leaf certificates. Candidate source, not an accepted full proof, is preserved in this dossier. 
