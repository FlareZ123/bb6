# Raw108: six-hole frontier cylinder

Parent `1RB---_1RC---_0RD---_1LD1RE_---1LB_------`; first query B1 at ordinary time 7. The root cut leaves 20 nontrivial children. All 20 children now have candidate dispositions; the final 0LB witness has passed original-source Lean certification; **the unconditional parent bound is not established**. The candidate bound must accommodate long halters beyond the early 7014 cutoff, especially 0LE (192168).

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
| 0LB | 4136180 | 3890 |

The already accepted original-source audits include 0RD/186 ([45534584949](https://github.com/FlareZ123/bb6/actions/runs/45534584949)), 0LC/108 ([45534857294](https://github.com/FlareZ123/bb6/actions/runs/45534857294)), 1RC/147 ([45535246195](https://github.com/FlareZ123/bb6/actions/runs/45535246195)), 1RD/111 ([45535435037](https://github.com/FlareZ123/bb6/actions/runs/45535435037)), and 1RA/228 ([45610117731](https://github.com/FlareZ123/bb6/actions/runs/45610117731)). The 0LE #1279/#1280 counter proofs passed [45550931959](https://github.com/FlareZ123/bb6/actions/runs/45550931959). The sharded run [45699436782](https://github.com/FlareZ123/bb6/actions/runs/45699436782) additionally accepted `small` (1LC, 0RD, 0LC, 1RC, 1RD, 0RE), `lf1`, `le1`, `lf0` and `cut`; these are nine distinct full-child certificates plus the root cut, with retained artifacts. Together with the separate 1RA audit there are ten source-accepted child bounds. The other five shards were cancelled or failed. `medium1` failed on the 0RA open-list digest, now corrected and independently reproduced with 460 open entries; `le0` failed on recursion depth at its long halter.

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

## 0LB: final candidate leaf solved

The 3890-leaf roster has SHA-256 560bb574bb444f71d13cd205a95bd74f8879b36a0501a54a00a95241497b7508. The compressed base descriptor plus [extra overlay](0LB-extra.json) account for 3889 leaves, including all 24 ordinary continuations of delayed split #1930 (time 91502, A1). Its longest observed continuation reaches the last hole at 4136174 ordinary steps. Candidate bound 4136180. The last leaf #2822 now has a four-phase positive-return induction for all natural parameters, entered from blank at step 1828. See [the recurrence](Gap2822.md) and [Lean source](Raw108LB2822.lean). The original-source adapter and recurrence passed [45695725613](https://github.com/FlareZ123/bb6/actions/runs/45695725613); the full 0LB audit is a separate acceptance gate.

## 0LE: exact packed pair sweeps for the two late halters

The two late first-hole queries #1276 and #1313 reach F1 at 192167 and 191383 ordinary transitions. The shared B-state pair transitions admit inductive left/right transfers over arbitrary packed natural tails: consuming a base-four digit 3 on the left writes digit 1 on the right in two steps, and the reverse transfer restores digit 3 with the scanned zero retained. See [Raw108LEFastCore.lean](Raw108LEFastCore.lean) for the two universal transfer lemmas and instruction-list soundness. [generate_le_trace.py](generate_le_trace.py) emits 51 and 50 short checked chunks respectively and balanced joins with exact costs. Both complete packed traces passed local Lean 4.36.0-rc2 against the copied packed transition definitions, with only standard axioms. [Raw108LERead.lean](Raw108LERead.lean) bridges the two exact table/time pairs to the original zipper; [Raw108LEAudit.lean](Raw108LEAudit.lean) substitutes only these queries in the standard audit. Original-source acceptance remains pending in [45718004491](https://github.com/FlareZ123/bb6/actions/runs/45718004491). No direct long replay is required for these two leaves.

## Remaining obligations

The 0LB descriptor is now consumed by the extended generator (including delayed split and n-gram/block witnesses); its first full audit [45696008658](https://github.com/FlareZ123/bb6/actions/runs/45696008658) failed; the newer generator uses the asymmetric n-gram search. The full 0LB shard still needs acceptance. For each completed child, the original-source `all_completions` theorem must be accepted. Integrate those weighted bounds with the root cut and the mixed-score canonical quotient; lift the small-cutoff branches to the maximum actual certified child bound (4136180 is the current conservative upper-bound candidate) or the attained champion score B.

Reproduce with `python generate.py <B1>` and manual `agent10-four-hole.yml` target `raw108-child`. The checker reconstructs the exact ordered census, replays each sweep, and checks the FAR masks and all leaf certificates. Candidate source, not an accepted full proof, is preserved in this dossier. 
