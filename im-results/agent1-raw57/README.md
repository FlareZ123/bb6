# Raw57 sibling closure: source-accepted children and the remaining parent branches

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

## Parent closure status — 2026-11-26 checkpoint

The source-accepted conditional bridge `Raw57ParentBridge.lean` (run 45752594597) proves the exact parent dichotomy: fourteen ordinary A1 choices have supplied weighted bounds, five choices close immediately, and only 1LA, 1LB, 1LE, 0LF and 1LF remain as residual children.

Four complete child Covers are now source-accepted:

| Child | Weighted bound | Original-source audit |
|---|---:|---|
| 1LA | 832 | [45762127475](https://github.com/FlareZ123/bb6/actions/runs/45762127475) |
| 1LE | 1,500 | [45767071990](https://github.com/FlareZ123/bb6/actions/runs/45767071990) |
| 1LB | 806 | [45783142807](https://github.com/FlareZ123/bb6/actions/runs/45783142807) |
| 0LF | 1,500 | [45783586050](https://github.com/FlareZ123/bb6/actions/runs/45783586050) |
| 1LF | 1,500 | [45818812585](https://github.com/FlareZ123/bb6/actions/runs/45818812585) |

The 1LB audit includes the final M211 prefix-rewrite invariant and the replacement M754 43-state RLE witness; its complete child theorem is `BB6.Agent1Raw57LB1.all_completions`. The 0LF audit completed the exact candidate partition with no residual entries; its child theorem is `BB6.Agent1Raw57LF0.all_completions`. These are child-cylinder Covers, not yet a parent Cover.

The last sibling is 1LF. Its exact open census has 2,973 leaves; the only two explicitly expected final tables are M882 and M885. Their shared proof uses a 104-state DFA, an eight-state symbol transducer, and a finite reachable product with 382 states (10 accepting product states). The independent checker `m882885_certificate.py` checks both the finite closure and exact arbitrary-tail zipper macros for the two table variants. Original-source sibling audit [45818812585](https://github.com/FlareZ123/bb6/actions/runs/45818812585) succeeded, establishing `BB6.Agent1Raw57LF1.all_completions` at bound 1,500.

The final parent consumer draft is `Raw57ParentComplete.lean`, theorem `BB6.Agent1Raw57Complete.parent_cover`, targeting `WeightedBound 1500`. It composes the five residual child Covers with the fourteen earlier branch bounds and five immediate cycles. The first full parent source-closure attempt [45823514994](https://github.com/FlareZ123/bb6/actions/runs/45823514994) was cancelled at 14:51:27Z after reaching the workflow's explicit 120-minute timeout; it produced no proof artifact and did not accept `parent_cover`. The existing manual workflow now gives only `parent-all` a 360-minute timeout, preserving the same source generator and exact dependency closure; one targeted retry is next. Until that retry succeeds, no unconditional Raw57 parent Cover is claimed.

## Canonical64 crosswalk and integration

The exact Raw57 parent is entry `canonical_index=33`, `raw_residual_index=57` of `im-results/agent13-roster-convergence/canonical-124.json`. Its address is B0=1RC, C0=0RD, D0=1LD, D1=1RE, E1=0LA, and its six-hole table is exactly `1RB---_1RC---_0RD---_1LD1RE_---0LA_------`. The address is canonical under `canonicalAddress 2`.

`Raw57Canonical64Membership.lean` proves unique `sameTable` membership in the accepted `Canonical64Raw120Integrated.roster64`, at zero-based index 33. It is deliberately membership-only: it defines no competing roster and makes no global soundness claim. This helper is not yet source-accepted. Agent31 has been notified to consume the parent through the existing Canonical64 stable-parent integration after the Raw57 parent Cover is accepted. The global residual count remains 64 until that integration itself passes.

## A1=1LE: source-accepted partition

<badge color="success">Source-accepted</badge> Lean CI run [45767071990](https://github.com/FlareZ123/bb6/actions/runs/45767071990) completed successfully on Lean 4.36.0-rc2; job 139730422389 compiled 1,998 project modules. The generated theorem is `BB6.Agent1Raw57LE1.all_completions`, proving the A1=1LE sibling at weighted bound **1,500**. Both `tree_checked` and `all_completions` have axiom profile `[propext, Classical.choice, Quot.sound]`.

The 3,326 open leaves were fully partitioned: 3,094 FAR, 106 sparse n-gram, 106 seeded pumps, 4 multi-seed pumps, 11 block-phase certificates, 1 late last-hole bound, and 4 custom proofs; no residual entries remain. The audit therefore closes the entire 1LE child cylinder.

Together with the earlier source-accepted 1LA bound 832 (run 45762127475), this leaves exactly three Raw57 parent children: 1LB, 0LF and 1LF. `Raw57ParentConsumerWithLALE.lean` is a composition draft that imports the two accepted child modules, lifts their bounds to the requested parent target, and leaves only those three Covers as hypotheses. The wrapper itself is not yet source-accepted; its generated 1LA/1LE modules must be regenerated in the final parent-consumer CI closure. I added a reusable `parent-three` dispatch target to `.github/workflows/agent6-raw57-siblings.yml`, which regenerates the fourteen early/middle modules plus 1LA and 1LE and compiles this wrapper. Audit run [45771759533](https://github.com/FlareZ123/bb6/actions/runs/45771759533) failed before proof checking with KeyError 'AR'. Commit [d76228c](https://github.com/FlareZ123/bb6/commit/d76228c4903078a12d3f4b9c11db941fefcaf258) repaired this by running `generate.py` (which creates the 0RA module) and removing the unsupported `AR` generator call. The old `parent-three` wrapper remains a conditional intermediate; the new `parent-all` run is the full parent proof attempt.

## A1=1LB: source-accepted complete sibling

The final M211 residual has a source-accepted finite exact prefix-rewrite certificate, [run 45780341512](https://github.com/FlareZ123/bb6/actions/runs/45780341512). Its 57 arbitrary-tail rules, regular-language closure and exact 14,922-step entry prove unbounded live prefixes for every compatible completion. See [M211PrefixInvariant.md](M211PrefixInvariant.md). The complete 1LB sibling audit then passed at weighted bound **806** in [run 45783142807](https://github.com/FlareZ123/bb6/actions/runs/45783142807), establishing `BB6.Agent1Raw57LB1.all_completions`.

## A1=0LF: source-accepted complete sibling

The complete 0LF sibling audit passed at weighted bound **1,500** in [run 45783586050](https://github.com/FlareZ123/bb6/actions/runs/45783586050), establishing `BB6.Agent1Raw57LF0.all_completions`. The exact first-hole census has 1,807 open leaves; the final generated specification has no residual hypotheses. The custom proofs include the M968 prefix-automaton certificate and M1242 quadratic growth invariant.

## A1=1LF: source-accepted complete sibling

The complete 1LF source audit passed at weighted bound **1,500** in [run 45818812585](https://github.com/FlareZ123/bb6/actions/runs/45818812585), establishing `BB6.Agent1Raw57LF1.all_completions`. Its 2,973 open leaves include the two final explicit tables M882 and M885, handled by the shared 104-state DFA / transducer certificate described above. The workflow ran `m882885_certificate.py` before generating and compiling the exact Lean sibling tree.

## A1=1LA: source-accepted partition

The exact side-cycle census is 2,258 splits, 32,018 cycle leaves, 15,943 last-hole leaves and 3,974 open leaves. The complete disjoint open-leaf partition is 3,703 FAR witnesses, 114 sparse n-gram proofs, 132 RLE automata, two pattern-RLE automata, two branching pumps, five late last-hole bounds and sixteen custom nonhalting residuals. The sixteen residual table indices are 270, 274, 276, 404, 407, 442, 443, 444, 462, 474, 475, 486, 748, 944, 2021 and 2172. The 748/944 alternating-counter pair, seven grammar proofs, two binary-counter proofs and the remaining arbitrary-tail zipper/word-grammar wrappers are imported by the existing generator; the final generated tree is checked against the exact original partial-table enumeration.

The source audit passed in existing workflow run **45762127475** using Lean 4.36.0-rc2. It compiled the exact dependency closure (2,214 project modules) and exported `BB6.Agent1Raw57LA1.all_completions` at weighted bound 832, with axiom profile `[propext, Classical.choice, Quot.sound]`. This is a proof-carrying bound for every completion of the 1LA child cylinder, not a decision of the whole Raw57 parent and not a global BB(6) bound. Reproduction is through `make_1la_spec.py` and `generate_sibling.py 1LA`; the exact custom proof sources and frontier inputs remain in this directory and `im-results/agent4-raw58/`.
