# Raw57 sibling closure: certified 0LB, 1RF, 1LC and conditional parent bridge

Parent raw57: `1RB---_1RC---_0RD---_1LD1RE_---0LA_------`. Child A1=1RF:
`1RB1RF_1RC---_0RD---_1LD1RE_---0LA_------`.

The exact first-hole enumeration using Agent47's fast enumerator gives 2073 splits, 37150 cycle leaves, 8686 last-hole leaves, 1844 open leaves. All 1844 open candidates are now covered by 1811 FAR witnesses, 31 one-block growth certificates, and the following two independently Lean-checked proofs. No unresolved discovery leaf remains. The sharp candidate weighted bound is 230 (halting table `1RB1RF_1RC0RA_0RD1RB_1LD1RE_HHH0LA_1LE0RD`, 229 ordinary steps, zero delay). The initial full source partition audit 45725993066 was interrupted by runner shutdown. The repaired, bounded-subtree audit **45752357170 passed**; `BB6.Agent1Raw57RF1.all_completions` certifies the bound. All five-hole compatible tables: 9,765,625.

## A1=0LB: certified partition

Child `1RB0LB_1RC---_0RD---_1LD1RE_---0LA_------`: 1381 splits, 23617 cycle leaves, 7526 last-hole leaves, 621 open leaves. Of these, 558 have FAR witnesses, 58 single-block sweeps, three double-block sweeps (156,303,325), and two sparse n-gram invariant proofs. All 61 sweep theorems and both n-gram nonhalting theorems compiled locally in Lean 4.36.0-rc2 against hash-verified original dependency objects from artifact 15057164854 with standard axioms only. The final source tree audit **45752353339 passed**. Certified weighted upper bound 225, with 224 ordinary steps and zero delay for `1RB0LB_1RC1RF_0RDHHH_1LD1RE_0RF0LA_1LA0RB`. The entire compatible canonical cylinder has 25^5 = 9,765,625 tables.

New DFA `00102342104` closes open indices 8,30,493. Remaining M344 `1RB0LB_1RC1LB_0RD0RF_1LD1RE_---0LA_1LA1RF` and M360 `1RB0LB_1RC1LB_0RD1RF_1LD1RE_---0LA_1LB0RC` have sparse n-gram invariants of widths 5 and 6, 1499 and 2132 configurations respectively. Left/right edge counts are 22/58 and 53/61. Existing original SparseNGram checker and emitter are reused; these are unbounded nonhalting proofs, not finite simulation claims.

Final source theorem: `BB6.Agent1Raw57LB0.all_completions`. Generate with the same command below substituting 0LB for 1RF. No global roster change is claimed.

## M660: grammar-based nonhalting

Table `1RB1RF_1RC0LB_0RD---_1LD1RE_1RF0LA_1LB0RA`. The only missing transition is C1.

Write P(z,m) for z zero bits followed by m one bits. Root state B with empty left zipper stack, right tape P(1,2)^2 W. The grammar for W has four recursive prefixes and four terminals:

| Symbol | Tape bits via P |
|---|---|
| pad | P(2,2) |
| zero | P(8,2) |
| one | P(2,3) P(5,2) |
| two | P(1,6) P(1,2) |
| end0 | P(8,3) |
| end1 | P(2,3) P(5,3) |
| end2 | P(1,6) P(1,3) |
| end6 | P(1,6) |

At primitive time 264, the blank run is exactly root(end0). The scan starts after 7 moves, with right header 01011 and left frame 01. The left scan mode stores one of 1,2,8 ones following a zero; previously committed frames have 2,3,9 ones. Scanning pad (8 moves) commits a frame and enters mode 2; scanning two (50 moves) commits a frame and enters mode 8. On zero (27 moves), start drain with one; on one (59 moves), start drain with pad two. The terminal actions replace end0 by end1 (27), end1 by pad end2 (59), end2 by zero end6 (107), and end6 by end0 (75). Drain pops frame 3 in 12 moves and prepends pad; pops frame 9 in 18 moves and prepends zero; final frame 2 plus blank-left return takes 20 moves. All these identities are proved for arbitrary untouched grammar tails by `rfl`. Structural induction on frames and input word proves positive-time root-to-root closure, then unbounded compatible live prefixes prove NeverHalts.

Source `Raw57RF660.lean.gz.b64` expands by base64 decoding then gzip decompression to `Raw57RF660.lean`, SHA256 bc51f061d17aeff420fb244478bdcab2fbba33f03f3449b02a04745b17c50884. Theorems `BB6Coverage.Agent1Raw57RF660.rootReturn` and `never` compiled with exact original dependencies under Lean 4.36.0-rc2, axioms only [propext, Quot.sound]. Commit b24e67c027fe66644adfedaa989eef7a8ec8b161.

## M734: four-phase linear growth

Table `1RB1RF_1RC1LA_0RD0RA_1LD1RE_---0LA_1LB0LF`. Entry at time 31 into A, left empty, right 11(001)^0 00001. Section 11(001)^n 00001 returns after 186+32n moves to 11(001)^(n+5) 00001. The four phases cost 31+8n, 37+8n, 55+8n, 63+8n; each uses exact arbitrary-tail block transfers and fixed rewrites. `BB6Coverage.Agent1Raw57RF734.never` compiled with same original dependencies, axioms only [propext, Quot.sound]. Source compressed as `Raw57RF734.lean.gz.b64`, SHA256 0991ac69fd0b93075cf816c06d376d9099c585b832e76edc440cca4176e78c85. Commit 9d31d3db4bda159ce1c0e8a9c1c680edf0331ba5.

## Reproduction

`python im-results/agent1-raw57/generate_sibling.py 1RF` generates exact Lean tree and source modules; spec records SHA256 of open list and witness bank, with machine strings at the two indexed proven leaves checked by the final tree. The existing workflow `agent6-raw57-siblings.yml` is extended to route 1RF through this generator. Final target `BB6.Agent1Raw57RF1.all_completions`. Other siblings remain separate.

## Parent closure status

The existing 1LC generator was also repaired by bounded-subtree sharding; audit 45752512017 passed, bound 272. Agent7's audits 45750969498 (1RA, 382), 45751244565 (0LD, 324), 45751715986 (0LC, 629) passed. The source-accepted conditional bridge `Raw57ParentBridge.lean` (45752594597) reduces the parent to five ordinary choices 1LA, 1LB, 1LE, 0LF, 1LF given fourteen branch bound hypotheses. `Raw57ParentConsumer.lean` supplies all fourteen named branch theorems but its integrated compilation is pending. No unconditional parent bound or global roster reduction is claimed.

## A1=1LA discovery frontier

Exact side-cycle algorithm translated to JS: 2258 splits, 32018 cycle leaves, 15943 last-hole leaves, 3974 open; candidate maximum weighted 832. The two JSON frontier files record 3703 FAR and 112 sparse n-gram candidates, leaving 159 indexed partial machines for symbolic/other proofs. These are discovery results, pending original-generator and Lean acceptance. Agent7 is coordinating the other four residual siblings.
