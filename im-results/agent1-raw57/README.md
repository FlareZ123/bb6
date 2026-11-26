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

## Parent closure status

The source-accepted conditional bridge `Raw57ParentBridge.lean` (run 45752594597) proves an exact parent dichotomy: fourteen ordinary A1 choices have supplied weighted bounds, five cycles close immediately, and only 1LA, 1LB, 1LE, 0LF and 1LF remain as possible residual children. The 1LA child is now source-accepted at weighted bound **832** (run 45762127475; theorem `BB6.Agent1Raw57LA1.all_completions`). This removes one of the five residual obligations. The 1LE candidate partition has no residual leaves and its exact-source audit is queued as run 45767071990 at bound 1500; until that audit passes, it remains a candidate rather than an accepted branch theorem. 1LB still has one explicit residual, M211; 0LF and 1LF still have live leaves. Agent7 is pursuing 1LB/0LF, and Agent4 is pursuing 1LF. `Raw57ParentConsumer.lean` supplies the fourteen earlier branch bounds and now includes `cover_at_target_from_four`: given the 1LA theorem at 832, it discharges that residual and leaves only four Covers (1LB, 1LE, 0LF, 1LF). This adapter is a source-level draft pending integrated compilation. No unconditional parent bound or global roster reduction is claimed.

## M211 residual diagnostic (finite evidence only)

The remaining 1LB residual in `agent7-1lb.json` is M211:
`1RB1LB_1RC0LE_0RD0RF_1LD1RE_1RA0LA_1RD---`. I added the reproducible standard-library script `m211_local_trace.py`. A 2,000,000-step trace ends in state C at head -15,710, with visited interval [-15,711,48], 4,491 ones, 122,538 C1 events and 122,538 F0 visits; no F1 was observed. Every observed C1 had right-neighbor 0 (zero C1 events with right-neighbor 1), so every observed F entry was F0. The first 40 C1 events also have left-neighbor 1.

A bounded-window over-approximation that nondeterministically fills the newly exposed far-edge cell still reaches abstract F1 for radii 1 through 9. Thus the simple local-window abstraction is too coarse; this does not refute a stronger invariant and is not evidence of concrete halting. These are finite computational observations only, not a nonhalting proof. They were sent to Agent7 as a possible diagnostic for the alternating-gap counter analysis.

## Canonical64 crosswalk: membership-only helper

The exact Raw57 parent is entry `canonical_index=33`, `raw_residual_index=57` of `im-results/agent13-roster-convergence/canonical-124.json`. Its address is B0=1RC, C0=0RD, D0=1LD, D1=1RE, E1=0LA, and its six-hole table is exactly `1RB---_1RC---_0RD---_1LD1RE_---0LA_------`. The address is canonical under `canonicalAddress 2`. Replaying the ordered canonical list and the accepted residual-index cuts gives 96 canonical entries -> 78 after Combined106 -> 76 after 107/114 -> 68 after 60/109/110/111/117/121/123/125 -> 65 after 71/77/81 -> 64 after 120. Raw residual 57 survives at expected zero-based position 33 in the 64-entry roster.

`Raw57Canonical64Membership.lean` is deliberately a narrow membership helper, analogous to Agent16's Raw118 helper: it proves the root transition, exact unique `sameTable` membership in `Canonical64Raw120Integrated.roster64`, and expected index 33. It defines **no new roster** and makes **no global soundness claim**. This helper is an intermediate draft in `im-results/`, **not source-accepted**; its exact `by decide` checks should be compiled inside the existing Canonical64 artifact-assembly/score-consumer workflow.

The global integration sequence already has Agent31's `Canonical63Raw112Integrated.lean` and Agent4's combined `Canonical62Raw112Raw58Integrated.lean`. Raw57 should not create a competing 64->63 route. `Raw57Canonical62Membership.lean` now records the proposed exact membership check in Agent4's combined roster62 (expected count 1, index 33), without defining a roster or soundness theorem. It is not source-accepted. If that check passes and the Raw57 parent Cover is source-accepted, coordinate a third-parent cut with Agent4 to produce roster61. The former `Raw57Canonical64Graft.lean` competing-roster draft was retired; do not reuse it.

## A1=1LA: source-accepted partition

The exact side-cycle census is 2,258 splits, 32,018 cycle leaves, 15,943 last-hole leaves and 3,974 open leaves. The complete disjoint open-leaf partition is 3,703 FAR witnesses, 114 sparse n-gram proofs, 132 RLE automata, two pattern-RLE automata, two branching pumps, five late last-hole bounds and sixteen custom nonhalting residuals. The sixteen residual table indices are 270, 274, 276, 404, 407, 442, 443, 444, 462, 474, 475, 486, 748, 944, 2021 and 2172. The 748/944 alternating-counter pair, seven grammar proofs, two binary-counter proofs and the remaining arbitrary-tail zipper/word-grammar wrappers are imported by the existing generator; the final generated tree is checked against the exact original partial-table enumeration.

The source audit passed in existing workflow run **45762127475** using Lean 4.36.0-rc2. It compiled the exact dependency closure (2,214 project modules) and exported `BB6.Agent1Raw57LA1.all_completions` at weighted bound 832, with axiom profile `[propext, Classical.choice, Quot.sound]`. This is a proof-carrying bound for every completion of the 1LA child cylinder, not a decision of the whole Raw57 parent and not a global BB(6) bound. Reproduction is through `make_1la_spec.py` and `generate_sibling.py 1LA`; the exact custom proof sources and frontier inputs remain in this directory and `im-results/agent4-raw58/`.
