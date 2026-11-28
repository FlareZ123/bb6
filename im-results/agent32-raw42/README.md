# Raw42: certified first-hole and unary-growth cuts

Parent `1RB---_1RC---_0RD---_1LD0LB_------_------` (canonical surviving raw index 42, path address 1RC,0RD,1LD,0LB), first query B1 at time 6. Seven unknown slots, 25^7 = 6,103,515,625 normalized raw completions (each halt is counted as one choice).

## Whole-child acceptance and remaining work

The following exact first-level Covers have already passed pinned original-source Lean CI. The previous discovery-only status below is historical.

| B1 | CI run | Artifact |
|---|---:|---:|
| 0RB | [46051022197](https://github.com/FlareZ123/bb6/actions/runs/46051022197) | 15225325950 |
| 0RA | [45994074344](https://github.com/FlareZ123/bb6/actions/runs/45994074344) | 15195228793 |
| 0RE | [45996645063](https://github.com/FlareZ123/bb6/actions/runs/45996645063) | 15198405532 |
| 1RB | [45996253830](https://github.com/FlareZ123/bb6/actions/runs/45996253830) | 15196792976 |
| 1LA | [46068374725](https://github.com/FlareZ123/bb6/actions/runs/46068374725) | 15232008579 |
| 1RA | [46068379812](https://github.com/FlareZ123/bb6/actions/runs/46068379812) | 15231804396 |
| 0LA | [46089669906](https://github.com/FlareZ123/bb6/actions/runs/46089669906) | 15242941581 |

0RB now has a **complete source-accepted Cover at weighted bound 1006**: CI 46051022197 exports artifact 15225325950 (and repaired group-5 artifact 15224134446), using the seven accepted CI shards and an explicit exact-source FastBiDFA module override. 1LA and 1RA are now complete original-source weighted Covers at bound 100006: the two successful recovery runs above consume all eight shards, including repaired 1LA group 7 (artifact 15232930887) and 1RA group 1 (artifact 15232297382). The 0LA recovery then succeeded at the same weighted bound 100006, reusing five accepted groups and closing groups 1, 3 and 7. Thus seven of the twelve canonical children have complete accepted Covers. The remaining five are 0LE, 1LB, 1LC, 1LE, 1RE. The arithmetic and original-machine theorem for 1LB/4828 is now proved locally by Agent4 (see below), but whole-child assembly is separate. No complete Raw42 parent or global roster reduction yet.

[Raw42CanonicalJoin.lean](Raw42CanonicalJoin.lean) provides the checked final interface: exactly 12 canonical residual B1 child Covers at a common bound B≥12 imply the full Raw42 parent Cover. It applies the existing weighted TNF fresh-state renaming theorem with support cut 4, so each of the four F aliases is discharged by its E representative; no independent proof for an alias is required. The conditional theorem and exact count compile locally, standard axioms only. This is a parent assembly interface, not a closed parent.

## Relation-labelled DFA quotient for 1LA/1RA assembly bottlenecks

The interrupted recovery jobs [46053090463](https://github.com/FlareZ123/bb6/actions/runs/46053090463) and [46053095897](https://github.com/FlareZ123/bb6/actions/runs/46053095897) stopped (exit 143) respectively at old list certificates Raw421LARun902 and Raw421RARun3138. They were below the old 50 KB conversion threshold. Direct conversion of the full 902 witness to the existing trie checker was also too expensive in the local test.

The new [minimize_bidfa.py](minimize_bidfa.py) labels each left DFA state by its exact set of (machine state, scanned bit, right state) allowed triples, and dually for right states. Refine each partition until both symbol transitions preserve classes; number the blank class zero. Project transitions, allowed edges and the abstract safety relation onto the quotient. Equality of relation labels ensures that any representative of a merged class can be substituted on either side of a permitted abstract configuration; the stable partition preserves pushed symbol transitions. The generator is untrusted: every projected witness is checked by the unchanged original-source FastBiDFA soundness theorem.

| Exact leaf | Old (left,right,configurations) | Quotient | Local Lean elapsed / peak RSS |
|---|---|---|---|
| 1LA/902 `1RB0LE1RC1LA0RD0LF1LD0LB1LC1RB---0RB` | (142,107,1652) | (71,72,601) | 9.05 s / 2,129,892 KB |
| 1RA/3138 `1RB1LE1RC1RA0RD0RF1LD0LB1LC0LA0RB---` | (155,54,2070) | (54,27,467) | 3.35 s / 1,509,280 KB |

Both original-source `live` theorems compiled with Lean 4.36.0-rc2, using exact FastBiDFA Git blob 9cc8be5b1b4afcd3c9cd87865b8a1e94095f1a2f and original core artifact 15195788488. Axiom profiles are [propext, Classical.choice, Quot.sound], no sorryAx or native_decide. Original generated source artifacts are 15195778487 and 15195733756. Reproduce by running minimize_bidfa.py on each original list module, convert_bidfa.py, then replacing the concrete proof `:= by decide` with `:= by decide +kernel` before compiling. Exact resulting source SHA256 values respectively 1f78626e80c6f3b3bd191af035ee443a3d1e542baaedf17b8728a44f0fa35561 and a309c647c292d1daf2b8bdd6fe74564868479abdfddaa532fe385f55db64cf5b.

The existing manual recovery target now reuses the seven accepted groups for each branch, including 1RA group 4 from the second run (proof source revision cb294f1cff71bb89fc063d8cce01c8f3a0b4d71c). It restores the exact previous generated source for those accepted modules; only missing imports may be replaced from their original list witnesses. It performs relation quotienting before trie conversion on expensive remaining witnesses and records before/after counts. Both whole-child recovery runs on source revision 4b3a61a7086128e9737ee10df1285fb30fa32739 completed successfully and exported the final artifacts listed above. These are accepted child Covers, not a new global roster removal.

## Completing interrupted 0LA and 1LC recovery

The first 0LA recovery [46069218549](https://github.com/FlareZ123/bb6/actions/runs/46069218549) failed in preparation, after validating five accepted shards, because the original assembly artifact had already converted some `Run` modules to FastCert and the minimizer accepted only list syntax. The simultaneous 1LC recovery 46069222731 was cancelled. [restore_fast.py](restore_fast.py) now decodes the exact trie edge and state relations into their list representation before quotienting; all final generated certificates still go through the unchanged original-source checker. The existing accepted modules remain untouched.

Local reproduction uses original generated artifacts 15226785430 (0LA), 15226735539 (1LC) and original core 15226315786. All 784 run-summary modules parsed and quotienting completed, including all three previously converted FastCert modules; their exact round-trip sets and transition arrays agreed. Run [test_restore_fast.py](test_restore_fast.py) on the two extracted artifact directories for the actual fixture check. The eight relevant alternate certificates below all compiled with Lean 4.36.0-rc2, exact Raw42 FastBiDFA source blob 9cc8be5b1b4afcd3c9cd87865b8a1e94095f1a2f, and only [propext, Classical.choice, Quot.sound].

| Branch/leaf | Old (left,right,relation) | Quotient | Lean seconds |
|---|---|---|---:|
| 0LA/1243 | (76,60,1226) | (20,21,129) | 1.01 |
| 0LA/2550 | (75,60,1175) | (19,21,126) | 0.88 |
| 0LA/365 | (115,33,1249) | (43,14,179) | 1.39 |
| 0LA/589 | (44,180,2601) | (31,102,1092) | 9.95 |
| 0LA/598 | (44,180,2567) | (31,102,1073) | 9.89 |
| 1LC/620 | (60,99,1351) | (32,48,496) | 3.22 |
| 1LC/9216 | (92,80,1864) | (32,28,395) | 2.14 |
| 1LC/631 | (103,37,2888) | (20,25,487) | 2.41 |

These check the concrete blockers and all preconverted large Run witnesses. The repaired 0LA recovery completed successfully ([46089669906](https://github.com/FlareZ123/bb6/actions/runs/46089669906)). The simultaneous 1LC recovery [46089674173](https://github.com/FlareZ123/bb6/actions/runs/46089674173) was cancelled but preserved accepted groups 0 and 6 (artifacts 15242360299 and 15243702497), in addition to original groups 2 and 3. Its exact generated sources are artifact 15240937855. Both new shard manifests pin revision 3a7aa1928d7caa6c6a6e64b4f1aa7b95276b2e53. The next recovery consumes these four accepted groups, builds only 1, 4, 5 and 7, and uses the unchanged eight-group consumer. The whole 1LC child remains unaccepted.

## Established original-source cuts

- [Raw42Cut.lean](Raw42Cut.lean) discharges the halt child at weighted bound 12, seven direct side-cycle children B1=0LB,0LC,0LD,0RC,0RD,1LD,1RC, and the symbolic B1=1RD child via [Raw42RDGrowth.lean](Raw42RDGrowth.lean). The latter starts after 9 steps in B with right word 0 followed by k=2n+3 ones; the positive return consumes 6k+5 steps and adds two ones. Arbitrary-tail transfers and unbounded iteration prove nonhalting of every completion. The first-hole partition closes 9 of 25 choices, leaving 16 ordinary children. It covers 2,197,265,625 raw completions.
- Inside the retained B1=0RA child, the next hole is A1 at time 9. A1=1LB next queries C1 at 11; C1=0RC yields [Raw42RAUnary.lean](Raw42RAUnary.lean). Seven primitive steps enter the exact zipper family A, left 0^(n+2) including the scanned cell, right 1^(n+2), n=0. A four-step entry, one right sweep, two-step turn, left sweep, and two-step finish take 2n+11 steps to n+1. This proves nonhalting of all completions of the four unknown E/F slots.
- A1=1LE next queries E0 at 10; E0=0LD yields [Raw42RAAlternating.lean](Raw42RAAlternating.lean). The seven-step blank entry is A, left 00, right 1^k (k=2). For every k=2n+2, a ten-step entry establishes the B right-transfer phase; k+1 three-step transfers and a six-step turn produce A with k ones on the left of two zeros and two ones on the right. Eleven-step A transfers move those k left ones to the right. Total 14k+19 primitive steps to k+2. Every untouched tail transfer is checked universally, including the boundary at empty left. Again all four unqueried slots may be completed arbitrarily.
- [Raw42RACuts.lean](Raw42RACuts.lean) proves equality to both exact path-derived Raw42 refinements, checks the four weighted query gates at 17, and exports `unary_cover` and `alternating_cover` for every bound B. These two disjoint descendants close another 2*25^4 = 781,250 normalized raw completions. Neither closes the whole B1=0RA child.

The first-hole cut and all three new modules were checked locally with Lean 4.36.0-rc2 against the exact imported source dependency objects from accepted Raw59 artifact 15054146521. Both new growth theorems report only propext and Quot.sound; both Cover adapters and query gates only propext, Classical.choice, Quot.sound. No sorryAx or native_decide. No fresh complete dependency CI acceptance is claimed. The new locally checked source SHA256 values are 917c06357eb33c53ec9762bedd2e31df4c9f39b4308da2de0116ea7965e92912, 0f41d9ab397c0c49444f3fc6dad5327aaf4b031b41c373f5f4ebfff2f476489f, fb5f0cb111f476d87ba3f0eb5f8d26e3a8498cb72df690ab281ab056853ef2b8 respectively.

## Certified wide two-choice growth cuts

[Raw42WideGrowth.lean](Raw42WideGrowth.lean) and [Raw42WideCuts.lean](Raw42WideCuts.lean) specify eight disjoint seven-transition partial tables, their exact blank entries, and positive return clocks. The family is in D with empty right tape and the left zipper word shown, where (n) starts at zero. The two-bit repetitions are indicated by parentheses.

| B1 | Additional choice | Blank entry | Family left word | Return steps |
|---|---|---:|---|---:|
| 0LA | A1=1RC | 16 | 001(11)^n111 | 12n+25 |
| 1LA | A1=0RD | 30 | 001(11)^n1111 | 14n+39 |
| 1LC | C1=0RB | 28 | 001(11)^n1111 | 16n+43 |
| 1LC | C1=0RD | 28 | 001(11)^n1111 | 14n+39 |
| 1RB | C1=1LC | 24 | 0011(11)^n11 | 8n+29 |
| 1LB | C1=1RC | 16 | 001(11)^n111 | 4n+17 |
| 1RE | E0=1LD | 20 | 001(11)^n111 | 12n+29 |
| 1RB | C1=0RC | 11 | (00)^n000011 | 4n+12 |

Each return increments n. The derivation decomposes it into two repeated-block transfers and fixed entry/turn/finish phases. Each transfer is a fixed primitive run over arbitrary untouched left and right tails. The symbolic simulator checks fixed phases without inspecting the repeated-word marker and transfers without inspecting either opaque tail. Exact recipes are in [wide_growth_recipes.json](wide_growth_recipes.json). The Lean implementation uses the original SweepPumping induction, with exact path-refinement equalities in the Cover adapters. The pinned source check [45993015276](https://github.com/FlareZ123/bb6/actions/runs/45993015276) passed all eight original-source Cover theorems and their standard-axiom checks. These eight subcylinders certify 8*25^5 = 78,125,000 additional normalized raw completions, without expanding the five remaining slots. The full Raw42 parent remains open.


### Nested and two-run growth extensions (accepted)

[Raw42NestedGrowth.lean](Raw42NestedGrowth.lean) and [Raw42NestedCuts.lean](Raw42NestedCuts.lean) add three more seven-transition cylinders:

- B1=1LB, C1=0LD: B with empty left, right 01^(n+2)01^(2n+2), entry 15, return 4n+21 to n+1. The two growing runs are tracked independently by arbitrary-tail transfers.
- B1=1LB, C1=0RD: B with empty left, right 01^b, entry 12 at b=4. Outer pass costs 4b+5 and enters B with right 1^b011. Inner pass maps 1^a01^c to 1^(a-1)01^(c+2), cost 4a+1; iterate to a=0. Hence b becomes 2b+2, total cost 2b^2+7b+5.
- B1=1LC, C1=1LC: same outer family and entry 14; inner state is C for a>0, B at a=0. Inner pass costs 4a+3, giving total return 2b^2+9b+5 and b becomes 2b+2.

The exact nested induction and Cover adapter passed [CI run 45993507004](https://github.com/FlareZ123/bb6/actions/runs/45993507004) on source revision 423208e5e23c300195d0cfffa9a730f9f084fbf8, with no nonstandard axioms. These three are disjoint from the previous eight, giving 11*25^5 = 107,421,875 additional raw normalized completions proved nonhalting. No full B1 child or parent closure is inferred.

## Early second-hole coverage: 93 additional nonhalting cylinders (local original-source check)

[Raw42EarlyNGram.lean](Raw42EarlyNGram.lean) closes 93 seven-transition cylinders with explicit asymmetric n-gram witnesses of widths at most three bits per side. It directly checks each certificate on the exact two-choice refinement of the authentic Raw42 parent, avoiding copied-table equality or a trusted discovery algorithm. The earlier eleven wide/nested growth Covers are imported and consumed at their exact refinement types. The ten second-hole query gates are checked at weighted bound 64, including the immediate halt choice.

| B1 | Second hole (time) | New n-gram Covers | Prior growth Covers | Remaining ordinary choices |
|---|---|---:|---:|---:|
| 0LA | A1 (20) | 10 | 1 | 13 |
| 0LE | E0 (7) | 9 | 0 | 15 |
| 0RE | E0 (7) | 9 | 0 | 15 |
| 1LA | A1 (9) | 11 | 1 | 12 |
| 1LB | C1 (8) | 9 | 3 | 12 |
| 1LC | C1 (32) | 9 | 3 | 12 |
| 1LE | E0 (7) | 9 | 0 | 15 |
| 1RA | A1 (9) | 13 | 0 | 11 |
| 1RB | C1 (8) | 10 | 2 | 12 |
| 1RE | E0 (7) | 4 | 1 | 19 |
| **Total** | | **93** | **11** | **136** |

The disjoint new early cylinders contain 93*25^5 = 908,203,125 normalized raw completions; the combined 104 nonhalting cylinders and ten bounded immediate halts contain 114*25^5 = 1,113,281,250. This count is disjoint from the initial nine-choice cut and the two 0RA cuts, but 19 of the 93 early cylinders (nine 0RE and ten 1RB) are already contained in the previously accepted whole-child Covers identified above. The other 74 may overlap previously investigated descendants. Thus this is a compact alternative proof and exact conditional decomposition, not 93 novel global exclusions. No fresh E/F symmetry factor is claimed. All remaining ordinary children are retained, rather than inferred nonhalting from a finite cutoff.

The exported `BB6.Agent32Raw42Early.cover_all` takes Covers of the exact 136 residual refinements at any B≥64 and returns Covers of all ten first-level parents. `bankCover` independently exports each n-gram leaf at arbitrary B; `count_new`, `count_residual`, `code_distinct` and `first_distinct` check the finite partition. Local Lean 4.36.0-rc2 compilation against original-source objects from artifacts 15054146521, 15193983498 and 15195400786 succeeded. The coverage theorems depend only on propext, Classical.choice and Quot.sound; the checked counts require no axioms. Source SHA256 e136d9bdbb4257f192d4cf90ccfbf67d5b7c4da625acb94ec086f5731b1ad191. No new CI acceptance claimed. The existing manual workflow has an early variant for a pinned source-closure audit.

**Next edge:** use `residual` to restrict discovery to the 136 exact subparents, join their eventual Covers through `cover_all`, and combine with 0RA/0RB and fresh-label transport. Do not re-discover these 104 nonhalting cylinders or treat the ten conditional parents as closed.

## Remaining problem and method

The 16 first-level children have 12 canonical representatives under fresh E/F renaming. A normalized first-hole discovery run using the existing [linear side-cycle scanner](../agent32-linear-side-cycle/README.md), cutoff 500, found 1723 retained leaves within B1=0RA alone (1523 with one unassigned slot, 184 with two, 14 with three, 2 with four). Both four-hole leaves are exactly the new inductive families above; the counts are untrusted search output before pruning and not a certified full tree. The promising route is to test uniform symbolic growth on highest-hole retained leaves before expanding, with FAR/prefix checkers for the remaining finite tree. Do not enumerate all six-state completions directly. The complete parent Cover and global roster consumption are still open.

## 0RA residual classification

At the same 500-step normalized search cutoff, 1723 open partial tables are partitioned into 1626 FAR discovery witnesses (DFA sizes at most five), three late trace candidates, 52 asymmetric n-gram proofs, and 42 remaining tables. FAR witnesses and the full discovery tree have not yet been assembled in Lean. The two symbolic four-hole leaves are independently FAR candidates as well; do not double-count them. The late traces are cycle candidates 310 (entry 311, period 656, left boundary 9) and 1655 (entry 2101, period 842, right boundary 1), and one last-hole query 497 at 622, slot 9, with a 623-step halting completion. These late witnesses are not yet checked in Lean.

The 52 exact tables and asymmetric widths are in [ngram42.tsv](ngram42.tsv). All 52 independently generated source modules compiled locally using Lean 4.36.0-rc2 and AsymNGram from accepted artifact 15054146521. Each proves `NeverHalts` for every compatible total machine, with only propext, Classical.choice, Quot.sound. No native_decide or sorry. Reproduce each module with `echo '<row>' | python emit_ngram42.py > Leaf.lean`, then compile against the original AsymNGram dependency. Generate separate files for parallel compilation; the single 446 KB combined file exceeded the local execution window. [emit_ngram42.py](emit_ngram42.py) reconstructs the finite closure and emits the actual Lean trie certificate; its search need not be trusted. Source generator SHA256 5336777eebd5eaf8db2503b8a0ab6cb9a0ff1667c2497b9241af2c0f7b2f1d7a, input SHA256 d56c31c6b9ac628d9a4c69d34e34fe113a3e4bec8e075824d541e9fa36861af0.

The [42-table residual roster](0RA-hard.tsv) was the input to the next stage; the size-six FAR exhaustive scan timed out, and asymmetric n-gram widths up to 16 with total width at most 24 found no certificate under the 100000-configuration cap. None of these failures proves halting. 

### Final exceptional leaves (0RA)

Of the 42-table residual roster, 39 have run/block-run DFA certificates regenerated by [run42.py](run42.py) (adapted from Agent32's Raw124 replay) and [emit_run42.py](emit_run42.py), with exact [table/parameter input](run42.tsv). All 39 modules individually compiled locally with Lean 4.36.0-rc2 against the original BiDFA checker from im-results/agent16-raw118/BiDFA.lean and the authentic SweepPumping dependency. All report only propext and Quot.sound. Reproduce each by piping a single row to emit_run42.py. BiDFA original source SHA256 7910c0960baaf2fd213c35510fff4e785219e97037c5268f4d528184086ee313, run42.py 5e5172d8bbddedf4c8a3f8bfa4e8b82fe2b617ba4ccf57b0a56b4cbe3a732305, emitter 8b4e5a68220f1a7ac174ee13772ed3c6b2f899d4097b4ca3b181524e3be7eff9, parameters ce4999aef033873bd32f07b39c4aaf1695c7475ac8778a71cab7cde89d30e7e1.

Leaf 1582 (`1RB1RE_1RC0RA_0RD0LF_1LD0LB_1LC1RA_0LD---`) and leaf 1665 (`1RB1RE_1RC0RA_0RD---_1LD0LB_1LF1RA_0LD0LF`) share the two-period growth family. At time 35 the zipper is A with scanned zero, left word 011(11)^n0101(101)^n including scanned cell, and empty right. A 10-step entry, 26-step transfer of each 11 block, 49-step middle phase, 2-step return transfer for each block, and 4-step finish take 63+28n primitive steps and increment both exponents. The arbitrary-tail transfers check for either table, so [Raw42RATwinGrowth.lean](Raw42RATwinGrowth.lean) proves nonhalting for all compatible completions of both. Local Lean check with propext and Quot.sound only, SHA256 055039e4777a47114e257a88622024c5c2e0374ba108cdd6461b46823072cfc4.

Leaf 1659 `1RB1RE_1RC0RA_0RD---_1LD0LB_1LF0RC_0LA0LF` is now **source-checked nonhalting for every compatible completion**, including all 25 normalized C1 choices. The exact return parser [Raw42Leaf1659.lean](Raw42Leaf1659.lean) and recursively synchronized word invariant [Raw42Leaf1659Invariant.lean](Raw42Leaf1659Invariant.lean) prove `BB6.Agent32Raw42RA.Leaf1659.never`; only propext, Quot.sound, local Lean 4.36.0-rc2 against artifact 15054146521. See [the return grammar and proof](Raw42Leaf1659Transducer.md). A five-bit block B=10010 commutes with the continuation map G; eight finite phase words P_i advance cyclically, sometimes recursively updating the tail, and four phases emit B. The finite exceptional suffix U0 generates B^4 P5 P6 U0 in eight G iterations. The regular language (B|P0|...|P7)*{U0,...,U7} is therefore closed, and a six-phase outer prefix plus twelve initial checked returns connects this directly to the authentic blank start. No finite scanning assumption remains.

All 1723 normalized open leaves of 0RA now have candidate verdicts. The 94 residual leaf proofs (52 n-gram, 39 run/block-run, 2 twin-growth, 1 recursive language) have been locally source-checked, as have the two independent four-hole growth proofs (also in the FAR class). The subsequently accepted whole-child CI run 45994074344 assembled all 1723 leaves and closes 0RA. No complete Raw42 parent or global roster reduction is yet claimed.

## 1LB exceptional leaves 18612 and 4828

The assembly generator now imports both locally checked original-machine nonhalting theorems directly, including Agent4's complete 4828 source decoded with its exact SHA256 digests. In discovery artifact 15195281779, the literal table at zero-based ID 4828 matches the registered proof. The remaining hard roster consists of seven block-FAR leaves, one late split (7667) with ten block-FAR open descendants, and the two direct symbolic leaves. This is an explicit candidate closure of the frozen hard roster; whole-child kernel acceptance requires the generated tree, all remaining certificates, and its final consumer.

[Raw42Leaf18612.lean](Raw42Leaf18612.lean) now proves the exact partial table `1RB1RA_1RC1LB_0RD1RE_1LD0LB_0RA0RF_---0RD` nonhalting for every compatible completion. At step 55 its family is D, left 00 1^(8n+10) 0 1^(2n+2), right empty, n=0. The three parameterized exact return moves on D-configurations (a,b,c) are reduce (a+4,b,c) to (a,b+2,c+2), clock 4a+10; swap-zero (0,b+4,c) to (b,2,c+3), clock 4b+11; and exit-two (2,b,c) to (c+4,b+2,0), clock c+12. The eight-stage composed return maps family n to n+1 at a positive clock. The failed CI 45996929823 was due to the locally dependent hypothesis in the two list-normalization inductions; clearing it and normalizing cons/append fixes the proof. Local Lean 4.36.0-rc2 against the exact assembly core reports only propext and Quot.sound for `BB6.Agent32Raw421LB.Leaf18612.live`. This closes the exact F0-hole leaf (25 normalized completions), not the entire 1LB parent. Fresh CI acceptance pending. Agent4 additionally completed the source-level nonhalting theorem for the other exceptional 1LB leaf 4828: exact table `1RB0RF_1RC1LB_0RD0RE_1LD0LB_0RA0LD_---0RD`, `BB6.Agent4Raw42Leaf4828.MachineProof.never` for every compatible completion. See [the finite forbidden-word invariant and original sweep bridge](Raw42Leaf4828Arithmetic.md). Both proofs need consumption at their exact generated leaf tables; no 1LB parent acceptance yet.

## 0RB complete local weighted Cover

**Theorem:** `BB6.Agent32Raw420RB.Closed.cover : Cover (WeightedBound 1006) p`, with `p` the exact partial table `1RB---_1RC0RB_0RD---_1LD0LB_------_------`. This certifies the entire 25^6 = 244,140,625 normalized-completion cylinder at the weighted bound. It does not assert a raw primitive time bound of 1006 before first-one normalization. No other Raw42 child is inferred closed.

The complete exact generated source from artifact 15194448129 was imported with the common accepted core 15195605495 and the seven successful shard artifacts of [run 45994080192](https://github.com/FlareZ123/bb6/actions/runs/45994080192): 15195277997, 15195173230, 15194314237, 15194998144, 15194854203, 15195028305, 15195755405. Their shared module identities agree. The missing 29 group-5 roots and 69 final assembly modules compiled locally using the matching Lean 4.36.0-rc2 binary. The final source theorem prints exactly `[propext, Classical.choice, Quot.sound]`. The toolchain binary hash is db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00. No sorryAx or native_decide.

The minimal source repair converts just Raw420RBRun1570 to [FastBiDFA](FastBiDFA.lean) via [convert_bidfa.py](convert_bidfa.py). On the exact tracked checker bytes (Git blob 9cc8be5b1b4afcd3c9cd87865b8a1e94095f1a2f), that leaf compiled with `lean -j1` in 21.63 seconds, peak 2,374,076 KB RSS. The containing exact refinement `pRoot_16_17_12` also has an independently exported [local Cover](Raw420RBRecoveredRoot.lean). To bound memory on large ordinary modules, [split_small42.py](split_small42.py) partitions the exact declaration blocks and retains each original module name as an import-only facade. Apply it to the six group-5 stems 22_05,18_16,16_08,04_22,16_16,22_04 (prefix Raw420RBClosedRoot_, suffix Small.lean). No declarations in the seven accepted shard closures are modified. The workflow's new `recover_rb5` variant restores precisely these artifacts, verifies nonoverlap, compiles only group 5 and the final consumer, and exports the shard before composition. Remote acceptance completed in CI 46051022197; the exported exact final Cover artifact is 15225325950. The earlier recovery run 46039522796 failed from a duplicate FastBiDFA module name; the repaired run pins the exact Raw42 checker.

Historical failures: run 45967480182 lacked reconstructed sources; 45968320615 was killed (exit 143); group 5 of 45994080192 failed. Neither is a mathematical counterexample. The original list BiDFA proof of leaf1570 consumed over 3.5 GB RSS after 56 seconds; the trie checker and split-module recovery avoid that blocker without a fresh search. Remaining objective: close the other retained children and use Raw42CanonicalJoin at a common weighted bound. No global roster reduction is claimed here.
