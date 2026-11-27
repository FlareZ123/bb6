# Raw40: local canonical coverage and outstanding obligations

Parent `1RB---_1RC---_0RD---_1LD1LA_------_------`, first unassigned A1 query after six ordinary transitions. The whole parent remains open. The original two-query canonical frontier contains 189 five-hole representatives; this is not the global cryptid roster. See the [historical evidence and individual child results](Raw40-history-pre-20261127.md) for earlier exact witnesses, compiler evidence and local refinements. The global accepted interface is maintained in the repository root README, independently of this dossier.

## Six-hole family status

| A1 | Weighted maximum | Status and source |
|---|---:|---|
| 0RC | 888 | Locally kernel accepted: [consumer](Raw40A0RC.lean), [rebuild](reproduce-A0RC.sh) |
| 0RD | 1132 | Locally kernel accepted: [consumer](Raw40A0RD.lean), [rebuild](prepare_a0rd.py) |
| 1RC | 5729 | Source accepted [CI 45854063610](https://github.com/FlareZ123/bb6/actions/runs/45854063610), [consumer](Raw40A1RC.lean) |
| 0RB | 637 | Candidate, several child proofs accepted; full consumer pending |
| 1RB | 1130 | Candidate, full consumer pending |
| 0LB | 75493794 | Complete certificate candidate, [CI 45939992957](https://github.com/FlareZ123/bb6/actions/runs/45939992957) failed on maxRecDepth in a 1LB audit shard |
| 1LA | 790 | Source accepted [aggregate CI 45943412131](https://github.com/FlareZ123/bb6/actions/runs/45943412131), [consumer](Raw40A1LA.lean) |
| 1LC | 7863 | Complete discovery classification; direct proofs locally accepted; full universal audit pending, [consumer](Raw40A1LC.lean) |
| 1LB | 19585 | Complete discovery classification; thirteen of sixteen children accepted; [consumer](Raw40A1LB.lean) |

The maxima are weighted first-hole scores in the repository convention; only an accepted universal consumer and attainment establish exactness. Other A1 families remain incompletely classified. None of the local bounds is a claim that BB(6) is solved.

## A1=1LA: full nine-child candidate

| B1 | Open leaves | FAR | Compact | Grammar | Weighted maximum candidate |
|---|---:|---:|---:|---:|---:|
| 0LC | 447 | 431 | 16 | 0 | 94 |
| 0LE | 1948 | 1849 | 99 | 0 | 498 |
| 0RC | 914 | 890 | 24 | 0 | 325 |
| 0RE | 3761 | 3585 | 173 | 3 | 702 |
| 1LB | 1010 | 999 | 11 | 0 | 107 |
| 1LC | 600 | 592 | 8 | 0 | 92 |
| 1LE | 2191 | 2118 | 73 | 0 | 644 |
| 1RC | 1433 | 1354 | 79 | 0 | 161 |
| 1RE | 5818 | 5616 | 202 | 0 | 790 |
| Total | 18122 | 17434 | 685 | 3 | 790 |

Attainment candidate `1RB1LA_1RC1RE_0RD1RC_1LD1LA_HHH0LF_1RC1LF`: 789 ordinary steps, halt, no delay. [Full consumer](Raw40A1LA.lean), [partition](Raw40A1LABase.lean), [generator](prepare_a1la.py), [rebuild](reproduce-A1LA.sh). Discovery banks `a1la-<B1>-discovery.json` retain exact literal tables and certificate data, so rebuilding does not rerun FAR discovery. The three special machines are proved by a variable-length unary-run grammar, not a cutoff or an affine-growth extrapolation; see [proof](A1LA-unary-grammar.md) and [Lean source](Raw40A1LAUnaryGrammar.lean). The three original-source nonhalting proofs passed Lean 4.36.0-rc2 in CI 45943030210. The aggregate passed CI 45943412131, establishing the exact weighted family maximum 790.

## A1=0LB: delayed halt and nonhalting certificates

[Late witness and hard leaves](A0LB-hard-leaves.md), [full candidate consumer](Raw40A0LB.lean), [generator](prepare_a0lb.py), [rebuild](reproduce-A0LB.sh). B1=1LB leaf561 reaches E0 at exactly 75,493,793 ordinary steps and attains weighted score 75,493,794 if E0 halts. The prior individual Lean proof is accepted; its enclosing family is not yet accepted. The accelerated checker avoids evaluating all 75 million steps in the canonical audit.

B1=1RE leaf198 has a compact 16/17 asymmetric n-gram certificate candidate with 2229 reachable configurations, 95 left and 581 right summaries and 735 predecessor edges; [data](a0lb198-compact.json). All 39 lag-bank leaves have finite closure candidates. These exploit lag-XOR followed by bounded run/residue summaries; exact tables and graphs are saved. The three multi-hole late queries are expanded rather than treated as nonhalting.

## A1=1LC: all twelve five-hole children classified at discovery level

All 122 initial opens have evidence: 105 FAR, 14 compact, and three [exact periodic-sweep mathematical proofs](A1LC0LC-periodic-sweeps.md). Candidate exact weighted score 106, with attainment at 105 ordinary moves plus halt, delay 0. [Lean recurrence source](Raw40A1LC0LCPeriodic.lean), [candidate exactness](Raw40A1LC0LCExact.lean), [generator](prepare_a1lc_0lc.py). The first CI accepted leaf39's individual theorem, but failed on list algebra for leaf95/118; all three repaired proofs passed CI 45944874921; the same build stopped at a reserved identifier in 0RC leaf88, since corrected and locally checked.

| B1 | Open leaves | FAR | Compact | Direct sweep/pump | Weighted candidate |
|---|---:|---:|---:|---:|---:|
| 0LC | 122 | 105 | 14 | 3 | 106 |
| 0RC | 467 | 427 | 39 | 1 | 321 |
| 1LB | 479 | 475 | 4 | 0 | 118 |
| 1RC | 308 | 292 | 16 | 0 | 298 |
| 1LE | 1093 | 1033 | 60 | 0 | 872 |
| 0LE | 1137 | 1061 | 75 | 1 | 794 |
| 0RD | 790 | 712 | 67 | 0 | 5756 (11 late queries) |
| 1LC | 77 | 77 | 0 | 0 | 107 |
| 1RD | 73 | 71 | 2 | 0 | 150 |
| 0RE | 2273 | 2140 | 127 | 3 | 7000 (3 late queries) |
| 1RB | 823 | 757 | 57 | 9 | 386 |
| 1RE | 2514 | 2377 | 124 | 3 | 7863 (10 late queries) |
| Total | 10156 | 9527 | 585 | 20 | 24 late queries |

For 0RC leaf88, entry at step563 followed by an exact 288-step prefix rewrite inserts 11110000, leaving all suffix bits untouched; [Lean proof candidate](Raw40A1LC0RCLeaf88.lean). The 0RC attaining witness includes one unit of blank delay. [Twelve-child rebuild](reproduce-A1LC0LC.sh), [0RC exactness candidate](Raw40A1LC0RCExact.lean), [1LB exactness candidate](Raw40A1LC1LBExact.lean), [1RC exactness candidate](Raw40A1LC1RCExact.lean). For 1LE the exact witness `1RB1LC_1RC1LE_0RD0LF_1LD1LA_HHH0RC_1RC0LB` reaches E0 after 871 ordinary moves and attains 872 with zero blank delay; its primitive halting and delay theorems passed local Lean 4.36.0-rc2 using the accepted Canonical77 bundle. The 60 compact candidates include seven previously unresolved unary-sweep machines (IDs 337–343); two-run summaries with unary length reduced modulo five close all seven finite graphs (392–524 live abstract states, 36–42 predecessor edges). [Literal bank](a1lc-1LE-discovery.json), [candidate exactness](Raw40A1LC1LEExact.lean). The 0LE last residual has a locally kernel-accepted [nested-sweep proof](Raw40A1LC0LELeaf1.lean): entry 145, positive epoch cost 150+56n, unary run growth by four per epoch. The 0RD eleven late leaves are all one-hole, with exact query times 2415–5755; their weighted maximum candidate is 5756, attained at leaf42. The three remaining children are completely classified at discovery level. In 1RB, five difficult machines are solved by an exact unary-run invariant with all six residues of the run length; the [search](parametric.py) and [proof generator](emit_parametric.py) produce thirty kernel-checked macro paths. Nine other machines have exact prefix-insertion proofs, generated by [emit_raw40_late.py](emit_raw40_late.py). The last 0RE holdout, [leaf388](Raw40A1LC0RELeaf388.lean), uses a nested four-phase run drain, with an exact outer recurrence k → 2k+2. These fifteen direct nonhalting theorems were accepted locally by Lean 4.36.0-rc2 with propext and Quot.sound only. The attaining 1RE table `1RB1LC_1RC1RE_0RD0RC_1LD1LA_0LD1RF_HHH0RA` has 7862 ordinary steps and zero delay; its exact halting proof passed local Lean via composable 256-step zipper segments. The three compressed recipes ([0RE](a1lc-0RE-recipe.json), [1RB](a1lc-1RB-recipe.json), [1RE](a1lc-1RE-recipe.json)) bind the complete canonical leaf rosters by SHA-256 and fix all FAR assignments and compact-summary parameters. The [parent consumer](Raw40A1LC.lean), [partition](Raw40A1LCBase.lean), and twelve child proofs are integrated by the [rebuild](reproduce-A1LC0LC.sh). Aggregate acceptance pending. No global roster decrement is claimed.


## A1=1LB: thirteen Lean-accepted exact children, all sixteen classified

| C1 | Opens | FAR | Compact | Late | Unresolved | Weighted score | Status |
|---|---:|---:|---:|---:|---:|---:|---|
| 1RD | 72 | 69 | 3 | 0 | 0 | 254 | Lean accepted |
| 1LB | 77 | 74 | 3 | 0 | 0 | 228 | Lean accepted |
| 0RD | 117 | 115 | 1 | 1 | 0 | 3760 | Lean accepted |
| 0LB | 119 | 116 | 3 | 0 | 0 | 97 | Lean accepted |
| 0LD | 235 | 218 | 17 | 0 | 0 | 245 | Lean accepted |
| 1LD | 219 | 219 | 0 | 0 | 0 | 114 | Lean accepted |
| 1RA | 147 | 145 | 2 | 0 | 0 | 124 | Lean accepted |
| 1LC | 314 | 312 | 2 | 0 | 0 | 135 | Lean accepted |
| 0RB | 336 | 326 | 10 | 0 | 0 | 192 | Lean accepted |
| 1RB | 259 | 248 | 10 | 1 | 0 | 1155 | Lean accepted |
| 1RC | 651 | 617 | 33 | 1 | 0 | 1927 | Lean accepted |
| 0LE | 892 | 846 | 46 | 0 | 0 | 436 | Lean accepted |
| 1LE | 948 | 936 | 12 | 0 | 0 | 331 | Lean accepted |
| 0RC | 1142 | 1095 | 43 | 2 | 0 | 1207 | Candidate (2 translated cycles) |
| 0RE | 2943 | 2835 | 101 | 5 | 0 | 19585 | Candidate (2 translated cycles) |
| 1RE | 2385 | 2275 | 108 | 1 | 0 | 1309 | Candidate (1 translated cycle) |

CI [45974645273](https://github.com/FlareZ123/bb6/actions/runs/45974645273) and [45977029623](https://github.com/FlareZ123/bb6/actions/runs/45977029623) both succeeded, including exactness and standard-axiom checks. 0RD attaining witness `1RB1LB_1RC0LE_0RD0RD_1LD1LA_1RF1LE_HHH0RC` halts after 3759 ordinary moves plus halt, delay 0. 0LE and 1LE both passed source/axiom acceptance in [CI 45987861313](https://github.com/FlareZ123/bb6/actions/runs/45987861313). 0RC's two previously unresolved leaves have explicit translated-cycle witnesses: ID122 entry 942, period 2255, rightward displacement 23, boundary −7; ID138 entry 897, period 595, leftward displacement −9, boundary −5. These exceed the original enumeration window of 256 transitions. The generator emits existing `.cycle` constructors directly; no new trusted checker is introduced. The complete candidate awaits Lean audit. The [0RE recipe](a1lb-0RE-frontier-recipe.json) binds all 2943 canonical entries by the exact roster hash: 2835 FAR candidates, 101 compact closures, 2 translated cycles and 5 late one-hole queries. The [1RE recipe](a1lb-1RE-frontier-recipe.json) similarly binds 2385 entries: 2275 FAR, 108 compact closures, 1 translated cycle and 1 late one-hole query. The 0RE attaining table is `1RB1LB_1RC0RF_0RD0RE_1LD1LA_0RC1LE_HHH1RB`, leaf1922, F0 after 19584 ordinary steps and zero delay. The 1RE candidate is 1309 (leaf382, F0 after 1308 ordinary steps). Their candidate upper bounds require source acceptance. C++ FAR discovery completed locally; encoded assignments are uint16 little-endian dictionary indices compressed with zlib, zero means no FAR witness. IDs and literal late/cycle witnesses are retained. The [sixteen-child consumer](Raw40A1LB.lean) and [partition](Raw40A1LBBase.lean) give complete discovery-level exactness candidate 19585. No global decrement is claimed.

[Rebuild](reproduce-A1LB.sh), [generator](prepare_a1lb.py), [0RC residual bank](a1lb-0RC-discovery.json).

## A1=0LA: complete discovery classification; source composition outstanding

The 0LB and 1LB children were already solved in Rounds5 and4 respectively; no rediscovery claimed. Newly saved C1 banks: 1LC 305 opens (281 FAR,22 compact,2 unresolved); 1RB 227 (181 FAR,24 compact,1 late,21 unresolved); 0RD 170 (149 FAR,17 compact,4 unresolved); 1LA 179 (144 FAR,32 compact,1 late,2 unresolved); 1RC 171 (146 FAR,22 compact,2 late,1 unresolved). These are discovery artifacts, not complete bounds. In particular 1RB leaf187 first queries F1 at1755, 1LA leaf129 at1138, and 1RC leaves64/65 first query E0 at1764; the initial enumeration scores must be increased appropriately. [1LC bank](a0la-1LC-discovery.json), [1RB bank](a0la-1RB-discovery.json), [0RD bank](a0la-0RD-discovery.json), [1LA bank](a0la-1LA-discovery.json), [1RC bank](a0la-1RC-discovery.json). The initial compact abstractions did not resolve hard 1LC leaves66/201 or 1RC leaf160. The [Agent42 crossing-splice/cycle bank](../agent42-raw40-crossing-splice/Bank.md) subsequently provided mathematical evidence for 28 of the 30 targeted residuals. The [leaf66 nested run-drain proof](A0LA1LC-leaf66-normalized-drain.md) now proves nonhalting of every E0 completion of that leaf: blank reaches X_11 after 93860 assigned moves, then X_n -> X_(n+1) for every n>=11. The finite replay passed in JS; the recurrence is a paper proof, not yet Lean accepted. The [leaf154 simultaneous crossing-splice proof](A0LA0RD-leaf154-two-pumps.md) proves the final targeted residual nonhalting: blank entry 132476 at head -480, two independent pumps, exact epoch 12262+520n with shift -24. Both finite entry and epoch checks passed in JS. All 30 residuals in Agent42's targeted bank now have mathematical evidence (28 from that bank and these two new proofs); source-level integration is still outstanding. The first five child banks are now completely classified at mathematical/discovery level; source integration remains outstanding. No global roster reduction.

The five compressed additional C1 recipes have 11 initially unresolved leaves: 0LE (1), 0RB (0), 0RE (7), 1LE (0), 1RE (3). The [late crossing-splice bank](A0LA-late-splice-bank.md) now proves all eleven nonhalting, with independent finite-premise replay passing all eleven. The final 1RE/1096 certificate uses three simultaneous pumps from state C0: entry483904, epoch271120+60256n, shift+336. All 41 targeted residuals (30 in the earlier Agent42 bank, plus these 11) now have mathematical evidence, including 13 results from the preceding mathematical discovery work. Candidate weighted maxima for 0LE, 0RB, 0RE, 1LE and 1RE are 11076, 1213, 22169, 10391 and 6966 respectively; none is an accepted upper bound yet. The [two-pump search](late_splice_multi.js) found five of the new certificates. No global roster reduction.

The [conditional parent consumer](Raw40A0LABase.lean) reuses the existing `a0LA` canonical tree, whose seven cycle branches and 0RC pump branch need no new search. It consumes exactly twelve five-hole child bounds, yielding candidate weighted maximum **22169**, with attaining table `1RB0LA_1RC0LF_0RD0RE_1LD1LA_0LB1RF_HHH0RC` (22168 ordinary moves, delay 0). Two children (0LB and 1LB) have earlier local kernel proofs; the other ten have complete discovery banks and await their source audits. The parent consumer itself is uncompiled. [prepare_a0la.py](prepare_a0la.py) materializes nine outstanding child audit candidates from the saved FAR/summary banks, translated cycles and crossing declarations; 1LC explicitly requires the missing leaf66 source rather than assuming it. It reuses the existing canonical enumerator and modular checker, and verifies the stored roster hashes where available. The generator has not been executed in this environment. The [orientation-aware integration](A0LA-late-splice-bank.md) supplies twelve candidate literal-source `never` declarations, including the reflected C-state return. No accepted parent bound or global roster reduction is claimed.

## Reusable mechanisms and baseline

[Portable canonical enumerator and compact closure](discover_compact.js), [FAR search](far_search.js), [compact Python emitter](compact_ngram.py), [graph minimizer](minimize_compact.js), [modular certificate integration](certify_modular.py). The trusted Lean checker independently reconstructs closure from supplied graphs. An accepted small graph is not itself an accepted parent audit: every canonical branch, early halt, late query and attainment must be included.

Three previously established five-hole pump families have exact entries and costs: 0LA/C1=0RC (entry9, 3n+2, 6n+13); 1LA/B1=0RD (entry8, 2n+3, 8n+17); 1LA/B1=1RB (entry8, 4n+3, 8n+15). See [Raw40Pump](Raw40Pump.lean), [Raw40MorePumps](Raw40MorePumps.lean). The unquotiented 303-cylinder frontier and 189-entry canonical frontier are distinct representations. The accepted local refinements must be composed through a checked consumer, not subtracted informally.

Next: accept the complete candidate family audits and remaining A1LB child proofs, repair actual compiler failures, and close the remaining families. Rebuilds use Lean 4.36.0-rc2 and the original Canonical77 dependency artifact 14997966221.
