# Raw57 A1=1RF: complete candidate partition, two new kernel proofs

Parent raw57: `1RB---_1RC---_0RD---_1LD1RE_---0LA_------`. Child A1=1RF:
`1RB1RF_1RC---_0RD---_1LD1RE_---0LA_------`.

The exact first-hole enumeration using Agent47's fast enumerator gives 2073 splits, 37150 cycle leaves, 8686 last-hole leaves, 1844 open leaves. All 1844 open candidates are now covered by 1811 FAR witnesses, 31 one-block growth certificates, and the following two independently Lean-checked proofs. No unresolved discovery leaf remains. The sharp candidate weighted bound is 230 (halting table `1RB1RF_1RC0RA_0RD1RB_1LD1RE_HHH0LA_1LE0RD`, 229 ordinary steps, zero delay). The full source partition audit is dispatched; **not accepted until it passes**. All five-hole compatible tables: 9,765,625.

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
