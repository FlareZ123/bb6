# Raw124 subcylinder work

Raw124 = `1RB---_1RC---_0RD---_1LD1RE_---1LF_------`. First new query F1 at 7 moves. Each fixed ordinary F1 row has 25^5 = 9,765,625 raw completions; the weighted checker handles early halts and initial blank delay.

## Current first-level branch status

The 23 directly source-accepted first-level F1 branches are listed below. The final F1=0LF branch is closed by the nested 0LF/F0=1RC composition. The complete parent theorem `BB6.Agent2Raw124ParentComplete.parent_cover` is now source-accepted at weighted bound **4,136,175**, covering all **24 of 24** first-level branches: [run 45908591612](https://github.com/FlareZ123/bb6/actions/runs/45908591612), artifact 15159377345, SHA-256 `9ec5b5b86fe4f78d636fd9a37891cabdd0017c04c8fc62f74f4ef6022ffcfa15`. Its axiom profile is exactly `propext`, `Classical.choice`, and `Quot.sound`. The 13 entries accepted in legacy replay run 45840496976 were individual matrix jobs; the overall matrix run failed because two *other* branches were terminated, so use each listed job/artifact as the evidence unit.

| F1 | Weighted bound | Accepted theorem | Source-accepted run / artifact |
|---|---:|---|---|
| 0RA | 283 | `BB6.Agent32Raw124Z0RA.bound_all` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980560426, artifact 15130748003 |
| 0RB | 272 | `BB6.Agent32Raw124Z0RB.bound_all` | [45841021688](https://github.com/FlareZ123/bb6/actions/runs/45841021688), artifact 15128037834 |
| 0RF | 71 | `BB6.Agent32Raw124Z0RF.bound_all` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980559902, artifact 15126744914; independently [45841208356](https://github.com/FlareZ123/bb6/actions/runs/45841208356) |
| 0LA | 5,910 | `BB6.Agent32Raw124ZeroLAComplete.bound_all` | [45839093000](https://github.com/FlareZ123/bb6/actions/runs/45839093000), artifact 15127830252 |
| 0LB | 4,136,175 | `BB6.Agent2Raw124ZeroLBComplete.bound_all` | [45827503893](https://github.com/FlareZ123/bb6/actions/runs/45827503893), artifact 15122105407 |
| 0LC | 145 | `BB6.Agent32Raw124Z0LC.bound_all` | [45841021688](https://github.com/FlareZ123/bb6/actions/runs/45841021688), artifact 15128591873 |
| 0LD | 157 | `BB6.Agent32Raw124Z0LD.bound_all` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980560502, artifact 15129710694 |
| 0LE | 3,006 | `BB6.Agent2Raw124New0LE.bound_all` | [45836460043](https://github.com/FlareZ123/bb6/actions/runs/45836460043), artifact 15129435887 |
| 0RC | 2,759 | `BB6.Agent32Raw124Z0RC.bound_all` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980560280, artifact 15127807592 |
| 0RE | 2,473 | `BB6.Agent2Raw124B0RE.bound_all` | [45884922679](https://github.com/FlareZ123/bb6/actions/runs/45884922679), artifact 15149067775 |
| 0RD | 267 | `BB6.Agent32Raw124Z0RD.bound_all` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980560352, artifact 15127941805 |
| 1LA | 6,230 | `BB6.Agent2Raw124New1LA.bound_all` | [45837006401](https://github.com/FlareZ123/bb6/actions/runs/45837006401), artifact 15128682403 |
| 1LB | 3,006 | `BB6.Agent2Raw124OneLBComplete.bound_all` | [45800254828](https://github.com/FlareZ123/bb6/actions/runs/45800254828), artifact 15107525242 |
| 1LC | 102 | `BB6.Agent32Raw124Z1LC.bound_all` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980560448, artifact 15128955411 |
| 1LD | 7 | `BB6.Agent32Raw124Trivial.bound1LD` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980560212, artifact 15132051672 |
| 1LE | 670 | `BB6.Agent32Raw124Z1LE.bound_all` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980560359, artifact 15130088173 |
| 1LF | 290 | `BB6.Agent32Raw124Z1LF.bound_all` | [45855224384](https://github.com/FlareZ123/bb6/actions/runs/45855224384), artifact 15134859375 (SHA256 `c8f36170937e1add82bdb53660a8c131ba390cb3b7f3da2291dfaf7dd75a80b7`) |
| 1RA | 1,029 | `BB6.Agent32Raw124Z1RA.bound_all` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980560453, artifact 15130536056 |
| 1RB | 184 | `BB6.Agent32Raw124Z1RB.bound_all` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980560344, artifact 15130193900 |
| 1RC | 688 | `BB6.Agent32Raw124Z1RC.bound_all` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980560355, artifact 15129256141 |
| 1RD | 80 | `BB6.Agent32Raw124Z1RD.bound_all` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980560372, artifact 15128635425 |
| 1RE | 7 | `BB6.Agent32Raw124Trivial.bound1RE` | [45840496976](https://github.com/FlareZ123/bb6/actions/runs/45840496976), job 139980560212, artifact 15132051672 |
| 1RF | 140 | `BB6.Agent32Raw124Z1RF.bound_all` | [45841021688](https://github.com/FlareZ123/bb6/actions/runs/45841021688), artifact 15127612983 |

The legacy batch's source revision is `2a0106d3bfbc4254872e122e6a95cccccdda1639`. Its successful branch jobs ran the source-closure and standard-axiom gates and uploaded the listed artifacts. The `legacy (trivial)` artifact checks both 1LD and 1RE. The 0RE and 1LF jobs in that batch were shut down. Separately, run [45841021688](https://github.com/FlareZ123/bb6/actions/runs/45841021688), source commit `4542dafbc48b00debeb80e248cc8d6c3a3ea6dc2`, accepted the three recovered branches 0LC (145; artifact 15128591873), 1RF (140; artifact 15127612983) and 0RB (272; artifact 15128037834), each through the original-source and standard-axiom audit. F1=1LF was subsequently replayed through the shared six-shard `weighted-tnf-raw124-legacy-sharded` target; all six shard jobs and the final assembly succeeded in run [45855224384](https://github.com/FlareZ123/bb6/actions/runs/45855224384), producing artifact 15134859375. The old shutdowns are superseded by these accepted replays. 0RE was recovered through independently checked sparse FAR certificates and exact subtree assembly; see [Agent4's recovery dossier](../agent4-raw124-0re/README.md).

**Accepted parent frontier:** The 22 initially accepted siblings and first-query halt case compose at weighted bound **4,136,175** in [Raw124ParentPartialCut.lean](Raw124ParentPartialCut.lean), [45884318889](https://github.com/FlareZ123/bb6/actions/runs/45884318889). The nested 0LF cut [Raw124ParentNestedCut.lean](Raw124ParentNestedCut.lean) passed [45885246108](https://github.com/FlareZ123/bb6/actions/runs/45885246108). After the complete 0RE proof passed, [Raw124ParentSingletonCut.lean](Raw124ParentSingletonCut.lean) was accepted in [45886398593](https://github.com/FlareZ123/bb6/actions/runs/45886398593), artifact 15149013566 (SHA256 `605078b6f833f6aa1a0db8a9a2f195eb5adad5eb0811c46b30a52b0b87841ccb`). Its theorem `BB6.Agent2Raw124ParentSingletonCut.cover_of_last` reduces the entire parent to exactly one remaining cylinder:

```text
1RB---_1RC---_0RD---_1LD1RE_---1LF_1RC0LF
```

The last 390,625 literal completions have a complete candidate census from Agent12. Their independently sharded source audit at bound 108,667 is accepted in [run 45887306671](https://github.com/FlareZ123/bb6/actions/runs/45887306671), artifact 15150950633. The full Raw124 parent Cover is source-accepted at 4,136,175 in [run 45908591612](https://github.com/FlareZ123/bb6/actions/runs/45908591612), artifact 15159377345. Its unique membership in the actual accepted `Canonical58Raw113Graft.roster58` and removal to form Canonical57 are now source-accepted in [run 45910336799](https://github.com/FlareZ123/bb6/actions/runs/45910336799), artifact 15159933665. See the [formal Canonical58→57 result](../../results/2026-11-26-raw124-canonical57-graft-agent2.md).

## Completed candidate branches

| F1 | Proposed weighted bound | Previously open leaves | FAR | Inductive | Late halts | Outstanding |
|---|---:|---:|---:|---:|---:|---:|
| 0RF | 71 | 42 | 42 | 0 | 0 | 0 |
| 0LC | 145 | 282 | 280 | 2 | 0 | 0 |
| 1RF | 140 | 1171 | 1160 | 11 | 0 | 0 |
| 0RB | 272 | 570 | 560 | 10 | 0 | 0 |
| 0RD | 267 | 143 | 141 | 2 | 0 | 0 |
| 1LC | 102 | 243 | 242 | 1 | 0 | 0 |
| 1RD | 80 | 861 | 859 | 2 | 0 | 0 |
| 0RC | 2759 | 374 | 362 | 11 | 1 | 0 |
| 1RC | 688 | 799 | 794 | 5 | 0 | 0 |
| 1LD | 7 | 0 | 0 | 0 | 0 | 0 |
| 1RE | 7 | 0 | 0 | 0 | 0 | 0 |
| 0RA | 283 | 656 | 633 | 23 | 0 | 0 |

F1=0RA is locally source-checked as described above. The other rows remain candidate audits unless separately promoted by an original-source acceptance recorded in the current status section. Together the displayed subcylinders represent 117,187,500 raw completions. The 0RC delayed last-hole encounter at step 2753 required increasing the proposed bound from 240 to 2759; the 1000-step exploration cutoff is never itself proof of divergence.

## Reproduction

Original four branches: generate_rf.py, generate_lc.py, generate_1rf.py, generate_0rb.py. Other eight: generate_bundle.py and compressed JSON witness bundles complete-bundle*.json.zlib.b64, including hashes of deterministic open leaf lists and trees, FAR automata, and symbolic operations. The generators produce source Lean Audit trees with explicit finite proof checks, partitioned to bound reduction cost. Manual agent13-coverage targets weighted-tnf-raw124-rf/lc/1rf/0rb/bundle are dispatched through GitHub Actions. Direct git clone DNS remains unavailable in this runtime.

Agent2MultiPump.lean extends Agent50's open-tail transfer lemmas to arbitrary finitely many repeated blocks, each with an independently quantified repetition count. A finite operation list proves an existential exact runtime and positive lower bound for every parameter environment. Its ordinary growth certificate uses all repetition counts n simultaneously. Agent2Nested.lean uses three independently quantified variables to certify nested counter loops for 1RF leaves 341 and 923. Local Lean 4.36.0-rc2 checked the general operational theorem, the eight initially collected multiblock certificates, both nested counter proofs, and all 21 single/multi witnesses in the seven-branch bundle against a reconstruction of the source executable tape semantics. Source integration adapters to NeverHalts and full source-level tree acceptance remain pending CI. No sorry or native_decide in the committed proof sources.

## Discovery improvements

0RB index 238 (zero-based in deterministic open.txt), `1RB0LF_1RC1LA_0RD0RF_1LD1RE_---1LF_0LA0RB`, had resisted exhaustive six-state DFA enumeration. A 32-state last-five-bit suffix DFA certified it, and congruence quotienting reduced it to nine states. It is now included in generate_0rb.py. Pooling successful DFAs across sibling branches yielded over a thousand new certificates. Enumeration and FAR search reused raw99/enumerate.cpp and agent11-tnf-raw86/search.cpp.

Automatic multiblock candidate inference uses four tape snapshots with constant growth increments, dynamic programming to segment into constant and repeated words, and finite symbolic search for exact sweep/rewrite operations. Proof checks do not trust the search. The complete Raw124 parent Cover is now source-accepted; Canonical58 subtraction remains pending exact membership in the accepted roster.


## F1=0LB — source-accepted complete branch Cover

The first 3,691-cycle / 508-hole scan was retracted: `enumerate.cpp` emits underscore-separated display tables, whereas `longcycle.cpp` indexes compact 36-character transition strings. The earlier scan passed display underscores through unchanged and its counts/certificates are invalid.

The corrected `generate_bundle.py` strips underscores before every C++ query and recursively resolves multi-hole hits: each such leaf becomes a 24-way `Audit.split`; translated cycles become `Audit.cycle`, and only genuine one-hole leaves become `Audit.last`. Open leaves are deferred until all descendants at the current cap are processed, then retried at a larger cap. Independent C++ batches now run in two processes.

The complete F1=0LB branch is now source-accepted. [Run 45827503893](https://github.com/FlareZ123/bb6/actions/runs/45827503893), artifact 15122105407, compiled the exact original-source closure and accepted `BB6.Agent2Raw124ZeroLBComplete.bound_all` at weighted bound **4,136,175**. The theorem composes the accepted partial cut with three exact late-residual weighted bounds: M264 at 520,988, M267 at 79,911 and M448 at 4,136,175. The older 17-residual census and local counter proofs below explain the construction; the accepted aggregate theorem closes the complement. This is only the F1=0LB child Cover; the full Raw124 parent is separately source-accepted at 4,136,175 in run 45908591612 and is now consumed into Canonical57 by run 45910336799.

## F1=0LF — source-accepted complete nested Cover

The exact F1=0LF first-hole dichotomy and its F0 parent cut are source-accepted in [run 45883981997](https://github.com/FlareZ123/bb6/actions/runs/45883981997), artifact 15148163947. The cut reduces the branch to the single exact F0=1RC child
`1RB---_1RC---_0RD---_1LD1RE_---1LF_1RC0LF`.

The final child is now source-accepted at weighted bound **108,667**. The independently sharded original-source audit [run 45887306671](https://github.com/FlareZ123/bb6/actions/runs/45887306671) compiled `BB6.Agent12Raw124ZeroLF1RC.bound_all` with axiom profile `[propext, Classical.choice, Quot.sound]` and uploaded complete closure artifact 15150950633 (SHA-256 `11ced53194ddc805456c51e1c75e6c3cfe41757b49e01a3e6e7acd08f4b65775`).

The exact nested parent composition is consumed by `BB6.Agent2Raw124ParentComplete.parent_cover`, source-accepted in [run 45908591612](https://github.com/FlareZ123/bb6/actions/runs/45908591612), artifact 15159377345. This closes F1=0LF and the entire 24-way Raw124 first-level partition at 4,136,175. No new search was required; the final source audit reused Agent12's existing witness bank and rich-audit partition.

### Historical cap-3000 discovery partition

For `1RB---_1RC---_0RD---_1LD1RE_---1LF_---0LF`, the initial versioned-tape search at cap 3000 and 32 candidate predecessors found 30,026 exact translated side-cycle leaves, 13,104 last-hole leaves, 1,961 splits and 1,974 open leaves. The respective completion masses were 8,475,650 cycle, 1,048,625 bounded (including halt choices at splits), and 241,350 open, totaling 9,765,625. The maximum observed hole query was at 2,925 moves. These are historical discovery counts, not the current accepted parent proof.

The first new hole is F0 at move 9. In its 1RB child, the partition has 75 splits, 1,379 cycle leaves, 287 last-hole leaves and 60 open leaves. Existing FAR search produces 53 candidate certificates among those 60. Reproducibility gap: the 60-open-leaf table list and 53 candidate FAR encodings are not currently stored beside this dossier; regenerate them from `fast_partition.cpp` before constructing a complete child `Audit` tree or making any aggregate closure claim. Two further one-hole leaves have parametric block-growth certificates in [Raw124ZeroLFBlockGrowth.lean](Raw124ZeroLFBlockGrowth.lean):

| Table | Entry moves | Left word (nearest first), parameter n | Increase per epoch |
|---|---:|---|---:|
| `1RB0RE_1RC1RA_0RD0RB_1LD1RE_---1LF_1RB0LF` | 91 | `0 (111011101110)^n 11101110111111` | 3 blocks of 1110 |
| `1RB1RF_1RC1RA_0RD0RB_1LD1RE_---1LF_1RB0LF` | 155 | `010 (11101110)^n 11101110111111` | 2 blocks of 1110 |

Both start in A with empty right list. `Raw124ZeroLFBlockGrowth.lean` proves universal nonhalting through the original `BlockPump.Certificate.never` adapter. CI run 45672467015, target `weighted-tnf-raw124-0lf-growth`, compiled the exact dependency closure (`BB6Coverage`, `SparseZipper`, `BlockPump`, and this adapter) under Lean 4.36.0-rc2. The exported `never1539` and `never1547` theorems have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom profiles. Each partial table covers 25 completions, so these two source-accepted proofs cover 50 completions. All five remaining hard leaves now have locally kernel-checked universal nonhalting proofs below. Those 53 FAR certificates were candidate discovery inputs only. Subsequent F0-specific source audits have accepted several child Covers; the remaining exact F0 complement and the late-query leaves above are now the active parent-assembly obligation.

The five exact residuals are the input to `search_0lf_hard_leaves.py`, which applies `cefar.cpp`'s counterexample-equivalence filter and canonical DFA enumeration through nine states (workflow run 45670238532). This is candidate discovery only: any hit must be emitted as a valid FAR certificate, kernel-checked, and connected to the original `NeverHalts` semantics before it can close the child. The companion `Raw124ZeroLFProbe.lean` is now a kernel-checked negative transfer result: `noTransferHard0` through `noTransferHard4` exhaust all 120 state relabelings fixing A, with and without reflecting the certificate's left/right tape orientation, for both existing block-growth certificates. None passes the exact certificate checker on any of the five residuals. This rules out reuse of these two certificates under those transformations; it does not itself establish halting or nonhalting for those residuals. The fifth is addressed independently below.

### Paired-word return invariant for hard4

`1RB0RD_1RC---_0RD1LA_1LD1RE_1RB1LF_1RB0LF` has an unbounded inductive proof in [Raw124ZeroLFPairReturn.lean](Raw124ZeroLFPairReturn.lean), commit `001a72a0ebe58c3f5ff6be56390eca2299d28dca`. At step 42 it reaches F0 with blank left and right word 00000 followed by paired bits. A forward phase consumes encoded 1 or 01, accumulating stack prefixes 11 or 1101; a terminal 00 (including implicit blank) adds one leading 1. The resulting stack consists of odd runs of at least three ones separated by single zeros. Each backward macro consumes one run and restores pair alignment, until a fresh section with the same invariant is reached. Both phases terminate by structural induction, and each full return takes positive time. Induction yields arbitrarily long live blank runs. `neverHard4` transfers those runs through the physical zipper embedding, and `coverHard4` provides the exact unweighted leaf for every bound; all 25 B1 completions are excluded by the proof. Local Lean 4.36.0-rc2 compiled the proof with `Frontier.lean` byte-identical to Git blob `115438c4f244b5416a91be4dd7a3f12103d5448d` and extracted source declarations from RootShift, SparseZipper and BlockPump. All four theorem axiom reports were `[propext, Quot.sound]`. Full original dependency closure and the weighted audit integration are not yet checked. No parent or roster closure is claimed.

### Growing-prefix counters for hard1 and hard2

The two tables with B1=1RF and E0=0RA or 1RA respectively admit a common prefix invariant: F0 with blank left and right word 0^8 (1100)^n 1111 followed by an encoded finite word. Their distinct carry transformations are formalized independently.

* [Raw124ZeroLFHard1.lean](Raw124ZeroLFHard1.lean), commit 8f7bd3f2ee50dfcd0935b639e6caf49c22faddb0: base-four digits (a,b) use twelve raw cells, including a lookahead flag h equal to the low bit of the next digit. The positive-time return increments the growing prefix exponent and performs base-four increment on the digit list. Blank entry at 54 moves.
* [Raw124ZeroLFHard2.lean](Raw124ZeroLFHard2.lean), commit d66c2ddcdb9f78ef6094d19d414b468352efab5b: alternating phase z and binary counter (v,xs), with fourfold higher-bit encoding. Arbitrary finite runs of carry bits are handled by induction, including implicit blank overflow. Blank entry at 850 moves.

The exported neverHard1/2 and coverHard1/2 are locally kernel-checked under Lean 4.36.0-rc2, using the same exact Frontier and extracted original zipper bridge declarations as hard4. Axiom reports [propext, Quot.sound]. Each of these two tables has only A1 unspecified. Together with hard4, these three proofs exclude 75 further completions. Full dependency-closure check and weighted child audit integration remain outstanding. No change to the canonical open roster is claimed.


### Redundant counter and typed gap stack (hard0, hard3)

* [Raw124ZeroLFHard0.lean](Raw124ZeroLFHard0.lean), commit 7689dd261ff615ec966689a9c5751af4e7d92918, table `1RB0LE_1RC1RA_0RD0RB_1LD1RE_---1LF_1RB0LF`: set Z=0000, O=11, X=0101. Two inductive word languages P ::= ε | ZP | OOP | XP | OZH | OXH and H ::= OP | ZH | XH capture the redundant carry representation. From a growing prefix 0^8 (1100)^n 1111 00 bb P, each positive-time macro return increments n and toggles b while preserving P. Blank entry at 194 moves. The E0 hole remains unqueried.
* [Raw124ZeroLFHard3.lean](Raw124ZeroLFHard3.lean), commit 5ef08b1799990e5073ec33e715d13f97cf567c76, table `1RB---_1RC1RA_0RD0RE_1LD1RE_0RB1LF_1RB0LF`: let e(n)=0^(4n+2)11 and o(n)=0^(4n+3)11; G ::= ε | o(n)G | e(m)o(n)G. The right word obeys G, with the current gap allowed to be offset by the scan phase. The left word is a stack of typed active/inactive runs, separated by one or two zeros; the run lengths modulo 4 depend on separator type and activation. Seven configuration constructors form a closed positive-time macro relation. Blank entry at 9 moves; no assumption that an excursion returns to the initial section is needed. The A1 hole remains unqueried.

Local Lean 4.36.0-rc2 checks of neverHard0/3 and coverHard0/3 report only [propext, Quot.sound], with the same exact Frontier/extracted bridge as the earlier proofs. All five new committed source blobs match their local checked versions. Thus all 125 completions of the five hard leaves have local semantic nonhalting proofs. The additional 50 completions of the two earlier growth leaves were already source-accepted. The full source dependency closure, tree check and weighted theorem remain separate integration obligations.


## F1=1LB — source-accepted complete branch Cover

The complete F1=1LB branch is source-accepted at weighted bound **3,006**: [run 45800254828](https://github.com/FlareZ123/bb6/actions/runs/45800254828), artifact 15107525242, theorem `BB6.Agent2Raw124OneLBComplete.bound_all`. The accepted closure consumes the cap-3000/lookback-32 partial cut and all eight exact one-hole residual certificates (five deterministic two-stack DFA proofs plus three explicit growth proofs). The partial-cut audit [run 45750346651](https://github.com/FlareZ123/bb6/actions/runs/45750346651), artifact 15085449694, remains one component of the accepted proof, not the final theorem. F1=1LB is now closed; the full Raw124 parent is source-accepted in run 45908591612 and is now consumed into Canonical57 by run 45910336799.

See [Raw124-1LB-fast.md](Raw124-1LB-fast.md) for exact residual table keys and reproduction. The targeted pump-search driver is [search_1lb_residual_pumps.py](search_1lb_residual_pumps.py); its dedicated CI target is `weighted-tnf-raw124-1lb-residual-pumps`. An extended `fast_partition.cpp` probe (cap 1,000,000; lookback 128) also returned `open` for all eight residuals, with no `cycle` or `last` leaf ([run 45767878144](https://github.com/FlareZ123/bb6/actions/runs/45767878144), artifact `15093027029`). This is bounded negative evidence only. Search output is exploratory until generated Lean `NeverHalts` proofs compile against the original source closure.


### F1=1LF — source-accepted complete branch Cover

The complete F1=1LF branch is source-accepted at weighted bound **290** for all 25^5 = 9,765,625 literal completions. The exact theorem is `BB6.Agent32Raw124Z1LF.bound_all`, with branch table `1RB---_1RC---_0RD---_1LD1RE_---1LF_---1LF`. The shared `weighted-tnf-raw124-legacy-sharded` target in `.github/workflows/agent13-coverage.yml` compiled all six child shards and the final assembly in [run 45855224384](https://github.com/FlareZ123/bb6/actions/runs/45855224384), source commit `932abe37df805f611eadcdd084f584a4c7046922`, artifact [15134859375](https://github.com/FlareZ123/bb6/actions/runs/45855224384/artifacts/15134859375), SHA256 `c8f36170937e1add82bdb53660a8c131ba390cb3b7f3da2291dfaf7dd75a80b7`. The final source audit requires the theorem's axiom profile to be within `{propext, Classical.choice, Quot.sound}` and rejects `sorryAx` and `native_decide`. This closes only the F1=1LF child; the full Raw124 parent is separately source-accepted in run 45908591612, but this branch result itself is not a Canonical58 subtraction.

## Canonical58 membership and 57-entry graft — source-accepted

The earlier `Raw124Canonical58Membership.lean` preflight was withdrawn and corrected. It imported `Canonical58SixParentMembership`, whose reconstructed six-parent list removes Raw59 and retains Raw118. That is **not** the source-accepted Canonical58 roster: the accepted chain consumes Raw58, Raw108, Raw115, Raw118 and Raw119 in Canonical59, then Raw113 in Canonical58, explicitly retaining Raw59 and excluding Raw118. A count of 58 did not detect this identity mismatch.

The corrected `Raw124Canonical58Membership.lean` imports `Canonical58Raw113Graft` and uses the exact accepted value `BB6.Agent31Canonical58Raw113Graft.roster58`. It defines Raw124 from the exact parent table in `Raw124ParentComplete`, proves unique membership in Canonical64 and the actual Canonical58 roster, lifts the parent Cover to 6,766,859, constructs the exact 57-entry successor with `removeParents`, and states the conditional `sound_integrated` and `exact_at_champion_score` consumers.

The combined consumer is source-accepted in Lean 4.36.0-rc2, [run 45910336799](https://github.com/FlareZ123/bb6/actions/runs/45910336799), artifact **15159933665** (22,949,946,864 bytes; SHA-256 `7c912dc7cff20dd796dad9e0008c6fbc9558f81bc9dcc13eb399b4393a73e140`). It imports the actual accepted `Canonical58Raw113Graft.roster58`, proves unique Raw124 membership, links the Raw124 parent closure with the exact kernel-declaration comparator, and constructs the 57-entry successor. The `sound_integrated` and `exact_at_champion_score` theorems passed the source/axiom gate. The checked-in source and wrapper match the frozen run revision `8f91f38a2ac75dbb2adef4ca82feb4ec694ef26e`; see the [formal result](../../results/2026-11-26-raw124-canonical57-graft-agent2.md).

A stronger follow-on consumer is also prepared in `Raw124Canonical56Graft.lean`. It imports the prospective `Canonical57Raw112Graft` (the Raw112 delta is still being source-audited) together with the now accepted Raw124 parent Cover, proves Raw124's unique membership in that actual Canonical57 roster, removes it to construct a 56-entry successor, checks Raw59 retained and Raw113/Raw112 absent, and states the corresponding conditional exactness theorem. This is also prepared only; it becomes eligible for CI once the Raw112 parent Cover is accepted. Agent32 and Agent17 have been given the source and the requested reuse path through the existing Canonical57 linked-closure job.
 
## F1=1LB numeric bridge

The branch-specific champion lift in [`Raw124OneLBChampionBound.lean`](Raw124OneLBChampionBound.lean) is now source-accepted in [run 45779181860](https://github.com/FlareZ123/bb6/actions/runs/45779181860). It transports only the F1=1LB cutoff 3,006 using the exact 27,959-step root-prefix theorem; it is not the general F412 two-million-step adapter and does not close any other F1 sibling.


### Direct long-run query probe

`probe_1lb_residuals.py` and [`simulate_1lb_residuals.cpp`](simulate_1lb_residuals.cpp) also ran a bounded 1,000,000,000-transition query probe ([run 45769587322](https://github.com/FlareZ123/bb6/actions/runs/45769587322)). That probe is not used as a nonhalting proof; the eight residuals are now closed by the exact source-accepted certificates in `Raw124OneLBComplete.lean`. Do not repeat the bounded probe.
