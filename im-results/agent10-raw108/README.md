# Raw108: six-hole frontier cylinder

Parent `1RB---_1RC---_0RD---_1LD1RE_---1LB_------`; first query B1 at ordinary time 7. The root cut leaves 20 nontrivial children. All 20 children have candidate dispositions and 18 have accepted original-source full-child bounds (0LA and 0LB remain); **the unconditional parent bound is not established**. The original-source attained lower bound is **4136175**, and the sharp upper-bound candidate is also 4136175 (the conservative full-tree cutoff remains 4136180). The candidate bound must accommodate long halters beyond the early 7014 cutoff.

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
| 0LE | 192169 | 2251 |
| 0LF | 1235 | 2784 |
| 0RF | 288 | 602 |
| 0LA | 26340 | 1956 |
| 0LB | 4136180 | 3890 |

The sharded run [45699436782](https://github.com/FlareZ123/bb6/actions/runs/45699436782) accepted `small` (1LC, 0RD, 0LC, 1RC, 1RD, 0RE), `lf1`, `le1`, `lf0` and `cut`. The resumed run [45718330365](https://github.com/FlareZ123/bb6/actions/runs/45718330365) accepted `medium1` (0LD, 1LA, 0RC, 0RA, 1RA) and `medium2` (1RF, 1LB, 0RF): 17 distinct accepted full-child certificates before the corrected 0LE audit. The corrected 0LE run [45731463516](https://github.com/FlareZ123/bb6/actions/runs/45731463516) accepted its full bound and attainment theorem, bringing the total to 18. The root cut is also accepted. Acceptance refers to successful shard jobs with retained artifacts, not to the conclusion of the entire matrix.

## 0RF: accepted certificate at weighted 288

The 602-leaf open roster (exact digest in [specs.json](specs.json)) has 586 FAR witnesses, 14 automatic positive-return witnesses, and two arbitrary-word grammar witnesses. In particular, the last non-FAR leaf #411 (`1RB1LA_1RC0RF_0RD0RC_1LD1RE_---1LB_0LA1LF`) has an exact inductive family at C, using the left list including the scanned cell:

```
C(1110000001111100000 (111000)^n 11111000111, 1^(53+18n))
  -- 1820+432n ordinary steps -->
C(1110000001111100000 (111000)^(n+1) 11111000111, 1^(53+18(n+1)))
```

The entry occurs at step 2862. All 14 automatic entry/growth proofs, including #411, passed local Lean 4.36.0-rc2 with the copied exact zipper/sweep core. The #62 and #115 arbitrary-word grammar proofs also passed locally, as did the separate 0LF #854 two-language grammar. The complete original-source 0RF bound has now passed in the resumed medium2 shard. No unresolved leaf is classified by a timeout.

## 0LA: complete candidate partition (source audit pending)

The ordered census of 1,956 open leaves is pinned by its SHA-256 digest in [specs.json](specs.json). The final specification uses a 76-code FAR bank, 128 symbolic positive-return witnesses, ten translated-cycle witnesses, four delayed first-hole queries, three prior manual counter proofs, and a width-six block-FAR witness for #114. The last candidate block saturation has 122 left states, 479 right nodes and 857 edges before minimization. Leaf #1099 has a 13-state ordinary FAR witness. Leaf #14 reaches its sole hole E0 after 26,334 transitions, so the candidate bound is raised to 26,340. Leaf #69 returns in 1026+756n steps, adding three copies of 00111011 to its retained list. These are candidate-level results until the original-source checker accepts the generated `all_completions` theorem.

## 0LB: final candidate leaf solved

The 3890-leaf roster has SHA-256 560bb574bb444f71d13cd205a95bd74f8879b36a0501a54a00a95241497b7508. The compressed base descriptor plus [extra overlay](0LB-extra.json) account for 3889 leaves, including all 24 ordinary continuations of delayed split #1930 (time 91502, A1). Its longest observed continuation reaches the last hole at 4136174 ordinary steps. The conservative candidate bound is 4136180; the source-certified attained lower bound is 4136175 via [Raw108LongAttained.lean](Raw108LongAttained.lean), CI [45718013441](https://github.com/FlareZ123/bb6/actions/runs/45718013441). The last leaf #2822 now has a four-phase positive-return induction for all natural parameters, entered from blank at step 1828. See [the recurrence](Gap2822.md) and [Lean source](Raw108LB2822.lean). The original-source adapter and recurrence passed [45695725613](https://github.com/FlareZ123/bb6/actions/runs/45695725613); the full 0LB audit is a separate acceptance gate.

## 0LE: exact packed pair sweeps for the two late halters

The two late first-hole queries #1276 and #1313 reach F1 at 192167 and 191383 ordinary transitions. The shared B-state pair transitions admit inductive left/right transfers over arbitrary packed natural tails: consuming a base-four digit 3 on the left writes digit 1 on the right in two steps, and the reverse transfer restores digit 3 with the scanned zero retained. See [Raw108LEFastCore.lean](Raw108LEFastCore.lean) for the two universal transfer lemmas and instruction-list soundness. [generate_le_trace.py](generate_le_trace.py) emits 51 and 50 short checked chunks respectively and balanced joins with exact costs. Both complete packed traces passed local Lean 4.36.0-rc2 against the copied packed transition definitions, with only standard axioms. [Raw108LERead.lean](Raw108LERead.lean) bridges the two exact table/time pairs to the original zipper; [Raw108LEAudit.lean](Raw108LEAudit.lean) substitutes only these queries in the standard audit. The original-source pair sweeps, exact traces, read equivalence and certified audit adapter passed [45718201577](https://github.com/FlareZ123/bb6/actions/runs/45718201577). The earlier run failed on a missing namespace, now corrected. No direct long replay is required for these two leaves.

The resumed 0LE audit failed specifically at Kid19 part31 because the proposed weighted cutoff 192168 is false. Leaf #1276 is `1RB0RF_1RC0LE_0RD1RB_1LD1RE_0RA1LB_0LB---`. Its last hole F1 is reached after 192167 transitions. E0=0RA permits an additional blank-delay transition into A; all incoming zero paths into A have length at most one in this complete halter. Consequently the attained weighted score is 192167+1+1=192169. The other five late leaves have weighted scores 2773, 2919, 2789, 191385, and 2544; every ordinary enumerated query is at most 1000 steps. The corrected sharp candidate is **192169**. [Raw108LEAttained.lean](Raw108LEAttained.lean) proves the lower-bound claim using the accepted compressed trace, and the full corrected bound, exact delayed score and lower-bound theorem passed original-source CI [45731463516](https://github.com/FlareZ123/bb6/actions/runs/45731463516). The revised audit also uses the accepted fast weight equivalence for short queries.

## 0LB: smaller proof burden and exact cutoff

The width-10 block alphabet now uses symbolic code bijection and membership rather than exhaustive Boolean splitting; the original-source bridge passed [45718800857](https://github.com/FlareZ123/bb6/actions/runs/45718800857). The nonhalting proof of leaf #895 via support-only wide block-FAR checking passed [45719411601](https://github.com/FlareZ123/bb6/actions/runs/45719411601). A width-2 exact-suffix alternative (six retained blocks) passed original-source checking in [45719980145](https://github.com/FlareZ123/bb6/actions/runs/45719980145).

The general necessary-and-sufficient weight-only audit checker and its fast short-query equivalence passed [45718013441](https://github.com/FlareZ123/bb6/actions/runs/45718013441) and [45719162851](https://github.com/FlareZ123/bb6/actions/runs/45719162851). [Raw108LBExact.lean](Raw108LBExact.lean) checks only the tighter weights on the already certified tree; [Raw108Exact.lean](Raw108Exact.lean) composes the proposed sharp parent theorem. Neither sharp upper-bound theorem is accepted yet.

## Remaining obligations: three proof shards and parent composition

The 0LA and 0LB audit candidates are complete. Seven of the ten first-move groups are source-accepted and retained: LA b/c/d in [45733599935](https://github.com/FlareZ123/bb6/actions/runs/45733599935), LB a/d/e/f in [45734378604](https://github.com/FlareZ123/bb6/actions/runs/45734378604). The missing groups are **la0-a, lb0-b (Kid06), lb0-c (Kid11)**. A complete 0LA or 0LB bound still requires every corresponding group. The last Kid11 retry [45746533439](https://github.com/FlareZ123/bb6/actions/runs/45746533439) reached a maximum-recursion-depth error in the generated Kid11 proof, and the Kid06 retry [45748159554](https://github.com/FlareZ123/bb6/actions/runs/45748159554) received runner signal 143. Neither diagnostic falsifies a candidate.

The new [fast kernel checker](Raw108FastCheck.lean), with [long-query adapter](Raw108FastCheckLong.lean), uses the existing proven short-weight shortcut and is extensionally equal to the original checkers for every partial table and Audit. It preserves all read, hole, weight, FAR, sweep and table-equality tests. Both modules were compiled locally in Lean 4.36.0-rc2 against the exact original-source modules from accepted LB a and LE artifacts; the four exported checker/query equality theorems depend only on propext, Classical.choice and Quot.sound. The new [modular generator](fast_kid.py) replaces the remaining groups' 180-node reductions with at most 49-node reductions and independent units targeting at most 100 audit nodes; each unit imports only its actual witness and proof dependencies. Concrete table replacement is checked by tableOK_sound. The final Kid name, Audit definition and check proposition are preserved, as is the shared child assembler. No accepted shard is regenerated for this change. On an existing genuine 180-limit Kid00 chunk, the original rfl reduction exceeded 15 seconds, decide +kernel took 9.65 s, the fast-weight checker 8.54 s and the literal-table version 7.30 s (single local measurements, not a global runtime guarantee). Four generated LB units including a join and a separate LA Kid passed local compilation. The new missing-group full audits remain unaccepted until their exact source runs pass.

The previous monolithic 0LA and 0LB runs hit runner limits. Width-10 #895 and all fourteen delayed #1930 nonhalting children already have accepted witness-level proofs; the narrower width-2 alternative for #895 is also accepted. The active witness specifications and original artifact integrity checks remain unchanged.

Once all missing groups pass, the existing raw108-compose target accepts a complete pin map (all historical accepted shards plus the three missing shards). It checks that generated assembler copies are identical, restores exact pinned object/source closures, and kernel-checks the two child assembly theorems and conservative parent bound 4136180. A further phase checks the sharp candidate 4136175 using the attained score and weight-only audit. No unconditional Raw108 parent bound or global roster cut is claimed before source acceptance.

Reproduce using the existing manual agent10-four-hole.yml target raw108-selected, with raw108_groups set to the JSON list of desired groups. No timeout is counted as classification.
