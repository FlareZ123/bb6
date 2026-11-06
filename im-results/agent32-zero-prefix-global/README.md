# Global raw-table frontier from physical traces and read-zero control paths

**Current status:** source-verified global certified-or-open partial proof trees; a **58.597775360%** exhaustive computational six-read-zero sufficient-certificate census; and a broader **68.066560000%** interpreted depth-four physical-trace frontier using exact finite lassos and finite-entry fresh-ray macros. The 68.06656% numerical count is a reproducible Lean VM report, while its source soundness and total-mass conservation are kernel checked; the numerical cardinality itself is not yet a separate kernel theorem. This remains intermediate infrastructure. BB(6) is unresolved. The previously known 43.907809280% zero-writer/directional nonhalting family comes from Agent44.

## Mathematical statement

Adopt Agent8's source formalization: a machine has 12 input rows, each with 25 possible actions (one halt, 12 write-zero ordinary moves, 12 write-one ordinary moves); an unassigned sparse input is distinct from an actual halt. Every run starts on a two-way all-zero tape in state A. Its Busy Beaver score includes the final attempted halting instruction.

Starting at A, follow the six read-zero control rows until their first halt or first repeated state. Record two separate sufficient properties of the successful transitions: (Z) every action writes zero, preserving a physically blank tape even if directions change; (D) every action moves in one fixed direction, preserving a fresh blank ray even if the machine writes ones. If Z **or** D holds through the first repeated control state, the actual blank-start machine never halts. If Z **or** D holds until a first encountered halt, that halt is physically reached, after at most five successful moves, and has exact step score k between one and six. All other cases remain unclassified by this particular first-event argument. The separate reversing-ray proof below handles a disjoint additional family. In particular, following read-zero transitions after a write-one and a reversal is only an enumeration choice; it is **not** treated as a valid machine simulation without a separate physical source certificate.

The first-repeat and first-halt cylinders are disjoint, and no path can visit seven new states. The raw-table counts, before any state renaming or tree-normal-form quotient, are:

| Distinct visited control states k | Nonhalting (Z or D) | Exact short halts (Z or D) | Unclassified |
| --- | ---: | ---: | ---: |
| 1 | 39,062,500 | 9,765,625 | 0 |
| 2 | 39,062,500 | 7,812,500 | 23,437,500 |
| 3 | 20,625,000 | 3,125,000 | 41,250,000 |
| 4 | 6,900,000 | 825,000 | 33,075,000 |
| 5 | 1,410,000 | 138,000 | 14,580,000 |
| 6 | 136,800 | 11,280 | 2,923,920 |
| **Total** | **107,196,800** | **21,677,405** | **115,266,420** |

Each entry counts assignments of the six read-zero input rows. Multiply by 25^6 for all completions of the six unread symbol-one rows. The exact full-table totals follow:

- Nonhalters: **26,171,093,750,000,000** (43.907809280%), all previously counted by Agent44.
- Exact score-at-most-six halters: **5,292,335,205,078,125** (8.879065088%).
- Disjoint decided family: **31,463,428,955,078,125** (52.786874368%).
- Unclassified in this conservative census: **28,141,215,820,312,500** (47.213125632%).
- Whole raw universe: **25^12 = 59,604,644,775,390,625**.

The 52.786874368% figure is the conservative first-event partition. Adding the independently source-certified reversing-ray sector below yields **32,417,103,271,484,375** classified tables (54.386874368%) and **27,187,541,503,906,250** tables outside these specified families. These are conservative classification counts, with no universal score upper bound or claim about the number of rooted hard holdouts.

## Exact counting derivation

Define Q_k as the product of (6-j) for j=1,...,k-1, and Q_1=1. An earlier successful control edge must reach a previously unseen state. The first repeated state has k possible targets; the terminal halt has one outcome. All remaining 6-k read-zero rows are arbitrary.

For first-repeat nonhalters, the number of read-zero assignments with k visited states is Z_k+D_k-I_k, with:

    Z_k = 2^(k-1)*Q_k * (2*k) * 25^(6-k),
    D_k = (2*2^k*Q_k) * k * 25^(6-k),
    I_k = (2*Q_k) * k * 25^(6-k).

Z enforces zero writes with arbitrary directions; D enforces one common direction with arbitrary writes; I is their intersection. This is exactly the union census already documented in [Agent44's dossier](../agent44-drift-closure/README.md).

For first-halt cylinders, the additional **disjoint** family of exact short halts has:

    HZ_k = 2^(k-1)*Q_k * 25^(6-k),
    HD_k = (k=1 ? 1 : 2^k*Q_k) * 25^(6-k),
    HI_k = (k=1 ? 1 : 2*Q_k) * 25^(6-k),

and per-k union HZ_k+HD_k-HI_k. At k=1 the condition on previous successful transitions is vacuous. Summing k=1,...,6 and multiplying by 25^6 gives the raw totals above. Every table has one first event, so no event class overlaps another.

Both [check-all.cpp](check-all.cpp) and [check-union.cpp](check-union.cpp) independently enumerate **all 244,140,625** possible read-zero assignment vectors, following the state control graph to its first event. The latter tests Z and D directly per assignment and checks all category counts against the independent closed formulas. The source checks completed successfully in [manual CI 42291433782](https://github.com/FlareZ123/bb6/actions/runs/42291433782).

## A disjoint two-transition reversing-ray sector

A sharper genuine-root proof uses a one-move finite prefix to enter an oppositely directed fresh ray. Let q be any of B,C,D,E,F and let dir be either right or left. Fix exactly two read-zero actions:

    A/0: write 0, move dir, enter q
    q/0: write 1, move opposite(dir), stay in q.

After the first ordinary move the machine is in state q at a fresh blank head cell, with its entire opposite-direction half-line still blank because A wrote zero. The assigned q/0 action then sweeps into that half-line forever, writing ones on cells it never revisits. All ten other input rows are unconstrained, so each certificate covers exactly 25^10 raw full-table completions. There are exactly ten such q/dir pairs; their A/0 actions are distinct, so the ten cylinders are pairwise disjoint and cover

    10 * 25^10 = 953,674,316,406,250 raw tables = 1.600000000%.

They lie entirely outside the first-event Z-or-D classification above: their rooted read-zero graph first revisits q after two transitions of opposite directions and mixed write bits. The previous first-event halt family is disjoint as these machines never halt. Consequently the mathematical guaranteed classified mass is

    31,463,428,955,078,125 + 953,674,316,406,250
    = 32,417,103,271,484,375 raw tables (54.386874368%).

[EntryControlAudit.lean](EntryControlAudit.lean) defines the ten exact two-slot tables, verifies each via the **original-source finiteRayOracle at prefix length one**, kernel-checks each cylinder mass 25^10, and constructs a stronger global certified-or-open frontier with an additional sound prefix-ray entry oracle. Its all-table exhaustiveness and total-mass conservation are Lean theorems; no unknown leaf is converted into a guessed halting verdict. A source CI job [run 42292636823, job 128149734164](https://github.com/FlareZ123/bb6/actions/runs/42292636823/job/128149734164) compiled the actual original Agent8/44/4 dependencies and these new theorems with only standard Lean axioms, no sorryAx. The exact first-action disjointness test is also source-formalized.

The finite-prefix ray mechanism is established prior infrastructure in [Agent44's prefix-drift theorem](../agent44-drift-closure/PrefixDrift.lean) and [Agent8's ray checker](../agent8-coverage-contract/RayFiniteOracle.lean). The ten-cylinder counting and global integration are intermediate applications; external novelty has not been established.

## Actual source-proof-carrying frontier

[ZeroPathAudit.lean](ZeroPathAudit.lean) defines the narrower global sparse frontier that follows known zero-writing actions only. Its first-free-input scanner is formally sound, and the raw-table frontier is exhausted by certified or explicitly open cases. [Source CI 42290328171](https://github.com/FlareZ123/bb6/actions/runs/42290328171) checked standard-only Lean axioms and computed the executable report:

    certified 14,857,432,861,328,125
    open      44,747,211,914,062,500.

[ControlPathAudit.lean](ControlPathAudit.lean) improves this to a global original-machine partial frontier incorporating three sound preexisting proof schemas: finite halting, arbitrary-direction zero-writer closure, and fixed-direction blank-ray closure. The scanner can follow a hypothetical read-zero control path after any assigned action, but it never infers halting or nonhalting from that hypothetical path. Each certified leaf is created only through Agent8/44's source-sound Boolean oracle. All other leaves are marked open.

Formally compiled theorems include scanControlPath_sound, directionalMaskOracle_sound, controlDecisionOracle_sound, globalControlPathAudit_exhaustive, and globalControlPathAudit_conserves, the last asserting certified mass plus open mass equals **exactly 25^12**. All passed full unmodified-source Lean 4.36.0-rc2 CI [42291051949](https://github.com/FlareZ123/bb6/actions/runs/42291051949), with only standard Lean axiom dependencies and no sorryAx. The globally exhaustive but **partial** Lean search tree is a real source proof object, not a search log.

**Verification boundary:** The 52.786874368% first-event count derives from a closed mathematical bijection and independent exhaustive C++. [ControlPathMassEval.lean](ControlPathMassEval.lean) evaluated the **actual** original-source sound global adaptive tree in [successful optional CI 42294578574](https://github.com/FlareZ123/bb6/actions/runs/42294578574). Its interpreted VM report is **31,789,073,486,328,125 certified** and **27,815,571,289,062,500 open** out of 25^12, or **53.333215232%** certified raw mass. Every accepted source leaf is a Lean kernel proof and total mass conservation is kernel checked. The numeric count itself is an interpreted Lean evaluator output, with no separate kernel-proved cardinality equality. This adaptive tree's 53.333% report is a different enumeration policy from the six-read-zero-row C++ classification at 58.597775360%. The C++/Lean pointwise predicates are not yet linked by an equality theorem.

## Six-read-zero-row global enumeration and broader computational census

[ZeroRowAudit.lean](ZeroRowAudit.lean) constructs a genuine globally exhaustive 25-way sparse branch tree over **all six read-zero input rows** of the source six-state machine. Every read-one row remains free. Each terminal is certified only by Agent8's original sound finiteDecisionOracle with bound six and finite prefix/ray search depth six; all other leaves are explicitly unresolved. Kernel-compiled globalZeroRowAudit_exhaustive and globalZeroRowAudit_conserves prove that every full raw table is either certified with a real nonhalting or score-at-most-six theorem or in an open leaf, and that the mass totals exactly 25^12. This source proof passed [manual CI 42294554955](https://github.com/FlareZ123/bb6/actions/runs/42294554955), with only standard axioms and no sorryAx.

The independent, fully deterministic [check-six-rows.cpp](check-six-rows.cpp) exhaustively enumerates all **244,140,625** read-zero transition vectors and checks the following explicit *sufficient* predicates directly against a finite tape:

- **Pristine zero-writing cycle:** first repeated state on a rooted zero-writing control path, any directions; original-machine nonhalting proof exists through zeroMaskOracle.
- **Short halt:** a physically simulated blank-root halt encountered before reading any unassigned symbol-one row, score at most six; original-machine proof exists through finiteHaltOracle.
- **Clean prefix-to-ray:** after at most six actual blank-origin moves, a physically fresh forward half-line and a closed constant-direction read-zero control graph exist; original-machine nonhalting proof exists through finiteRayOracle.
- **Open:** no such certificate in the tested finite search. This is not evidence of halting, nonhalting, or a hard cryptid.

Exhaustive C++ output, original-source CI run 42294554955:

| Outcome | Read-zero-row vectors | Full raw tables |
| --- | ---: | ---: |
| Pristine zero-writing cycle | 45,582,330 | 11,128,498,535,156,250 |
| Short halting | 23,011,245 | 5,617,979,736,328,125 |
| Finite-prefix clean ray | 74,467,400 | 18,180,517,578,125,000 |
| **Total classified** | **143,060,975** | **34,926,995,849,609,375** |
| **Still open** | **101,079,650** | **24,677,648,925,781,250** |
| **Total** | **244,140,625** | **59,604,644,775,390,625** |

The executable also partitions the **101,079,650 still-open read-zero tables** by the first reason the finite-prefix search cannot proceed: **95,287,330** (94.269548816% of its open set) need an as-yet-unassigned read-one instruction, while **5,792,320** (5.730451184%) reach the six-step prefix limit without a discovered certificate. This is a diagnostic of this particular finite search, not a lower bound on the number of genuine undecidable machines. Fresh-ray entry positions by completed blank-root steps 0 through 6 are **61,614,470; 9,628,450; 2,430,800; 667,920; 115,200; 10,560; 0**, respectively. The single-step entry count reproduces the independently counted entire one-turn sector exactly. Thus the dominant immediately actionable gap is **read-one branching on genuine physical traces** rather than further bare read-zero loop accounting.

The exact computed classified fraction is **58.597775360%** of all raw 12-input tables. The proof argument for each positive case uses the same invariant as the corresponding Lean original-source oracle. The C++ implementation never consults a read-one row, so each positive six-row cylinder really represents all 25^6 completions of read-one slots. The ten two-slot turning examples and the broader one-turn multi-state family are included within this more expansive finite-prefix search.

**Verification boundary:** Lean proves the actual global branch tree's soundness and mass conservation but does not kernel-prove its exact numerical certified mass. The above 58.597775360% is an exhaustive C++ count of semantically sound sufficient conditions, independently supported by the available original-source Lean certificates. A complete mechanical proof that the C++ predicate is pointwise equivalent to the compiled Lean oracle, or a feasible kernel-checked enumeration of all 244,140,625 Boolean oracle evaluations, would strengthen the numeric-to-formal bridge. Do not report this count as a kernel-certified cardinality equality or as a complete BB(6) classification.

The older adaptive [ControlPathAudit.lean](ControlPathAudit.lean) avoids filling all six read-zero rows, so its interpreted exact report can be smaller and is logically independent of the complete six-row mathematical census. It is retained as a resource-efficient proof-carrying search frontier. A manual-only option on [the CI workflow](../../.github/workflows/agent32-zero-path-global.yml) permits its expensive report evaluation without launching redundant work on every proof check.

## Physical-tape-guided read-one branching

The read-zero-only frontier has a sharp, measurable stopping point: 95,287,330 of its 101,079,650 unclassified six-row assignments (94.269548816%) physically encounter a symbol-one input for which this enumeration has no assigned transition. [PhysicalTraceAudit.lean](PhysicalTraceAudit.lean) is a stronger **all twelve-slot adaptive** global partial source proof object. Its scanner uses Agent8's original finite-support Turing-tape simulator, follows only assigned ordinary actions along the actual blank-origin trace, and branches on the earliest unassigned input slot **regardless of whether the scanned symbol is zero or one**.

The module proves more than syntactic first-unassigned correctness. Theorems `firstUnknownPhysical_has_prefix` and `firstUnknownPhysical_is_raw_prefix` construct an actual finite simulator run at whose endpoint the chosen slot is consulted, and use unmodified `finitePartialRun_sound` to prove that the same endpoint is reached in **every compatible original raw six-state machine**. Each certified terminal continues to require Agent8's existing source-sound finite decision oracle. Its globally exhaustive-or-open and exact 25^12 mass-conservation theorems therefore preserve the full old soundness standard. This is a **finite structurally bounded proof tree**, so open leaves remain open and it proves no global BB(6) bound.

As a concrete source-checked example, the sparse table A/0=1RB, B/0=0LA leaves A/1 completely free. The actual blank run writes a one at position zero, moves right, and returns left to read **A/1**. The new scanner proves the first free input is A/1 after two successful moves, while the read-zero-only control-graph scanner returns no unknown input at all. Theorems `readOneReturnTable_actual_first_unknown` and `readOneReturnTable_zero_only_scan_misses` exhibit this strict additional branch-discovery capability under the exact six-state source semantics.

The companion [ReadOneLeaf.lean](ReadOneLeaf.lean) specializes the same true blank run with A/1=halt, retaining **nine completely free table entries**. Its original-source finite halt oracle certifies the entire 25^9-cylinder as halting within three primitive steps. A stronger proof constructs the two-move finite-support tape and derives the **exact score three** from an assigned A/1 halting instruction in the raw semantics. This is a deliberately small source-contract regression test of real read-one branching, distinct from any hard holdout result. Its exact-score theorem and 25^9 cylinder mass **passed full unmodified-source Lean 4.36.0-rc2** in [CI 42297613493](https://github.com/FlareZ123/bb6/actions/runs/42297613493), with only standard Lean axioms.

This new source interface was verified with unmodified imported original Lean dependencies in [CI 42296568542](https://github.com/FlareZ123/bb6/actions/runs/42296568542) for the base physical scanner and [CI 42296717066](https://github.com/FlareZ123/bb6/actions/runs/42296717066) for the stronger actual-prefix bridge. The numeric certified mass of this larger physical-trace audit has **not** been evaluated; enumeration could in principle branch deeply into the 25^12 universe, and its generic exhaustive-or-open theorem by itself does not quantify how many leaves are decided.

## Exact finite lasso and finite-entry macro augmentation

[FiniteLassoOracle.lean](FiniteLassoOracle.lean) adds a source-sound exact recurrence test to the Agent8 finite-support simulator. It compares state, head, and the *represented infinite tape*, proving finite-support equality extensionally rather than comparing lists syntactically. A repeated full configuration in a fully assigned physical prefix implies a deterministic infinite run. The proof is connected to the original machine semantics through the existing `finitePartialRun_sound` theorem.

The concrete read-one-dependent witness is:

```text
A/0 = 1RB
B/0 = 0LA
A/1 = 0RB
```

After four ordinary moves, the machine returns to its exact initial configuration with blank tape. The existing finite halt / clean-ray / zero-writer decision oracle rejects this partial table; the new exact-lasso oracle accepts it. The three assigned entries define a nonhalting cylinder of exact mass **25^9 = 3,814,697,265,625**. The cylinder-mass equality is proved by Lean computation. This is a small regression witness for genuine read-one-dependent recurrence, not a hard-holdout resolution.

[LassoTraceAudit.lean](LassoTraceAudit.lean) combines three already sound decision mechanisms:

1. Agent8's finite halt, clean-ray, and zero-writer oracle;
2. the new exact finite-configuration lasso oracle;
3. Agent6's existing bidirectional `finiteEntryMacroBiOracle`, which detects a finite blank-origin prefix entering a fresh ray followed by a same-state translating macro.

The entry-macro theorem itself is reused from [Agent6's source](../agent6-fresh-glider/EntryMacroLeft.lean); this work integrates it into Agent32's *actual physical first-unknown* branching policy rather than claiming a new macro theorem. The global audit parameters are bound 6, finite ray limit 6, physical scan limit 12, exact lasso limit 12, entry limit 2, macro limit 4, and global tree depth 12. The source-checked example `entryToBExample_new_oracle_accepts` confirms that the combined oracle accepts Agent6's existing B-entry witness.

The combined audit has kernel-checked:
- `lassoDecisionOracle_sound`, combining the three source-sound oracle proofs;
- `globalLassoPhysicalTraceAudit_exhaustive`, proving every complete raw table is either `DecidedBelow 6` or belongs to an explicitly open leaf;
- `globalLassoPhysicalTraceAudit_conserves`, proving certified plus open report mass is exactly **25^12**.

Full unmodified-source Lean 4.36.0-rc2 verification passed after modular separation in [CI 42305551466](https://github.com/FlareZ123/bb6/actions/runs/42305551466). The combined macro integration and interpreted mass evaluation passed in [CI 42305017481](https://github.com/FlareZ123/bb6/actions/runs/42305017481). The numerical report at depth three is:

    certified 33,855,438,232,421,875
    open      25,749,206,542,968,750
    share     56.800000%

At depth four it is:

    certified 40,570,831,298,828,125
    open      19,033,813,476,562,500
    share     68.066560%

Both pairs sum exactly to **25^12 = 59,604,644,775,390,625**. The lasso-only depth-four audit had 38,071,441,650,390,625 certified tables (63.873280%); adding Agent6's entry-macro certificates contributes another **2,499,389,648,437,500** raw tables, or **4.193280 percentage points**. The integrated depth-four report exceeds the earlier six-read-zero C++ sufficient-certificate census (58.597775360%) by **9.468784640 percentage points**, and the earlier control-path interpreted report (53.333215232%) by **14.733344768 points**. These are different enumeration policies over the same raw universe; compare their certified raw-table masses, not their per-machine or holdout resolution rates.

### Bounded screen of the 663 historical holdouts

The reproducible screening tool [`scan-holdout-lasso.cjs`](scan-holdout-lasso.cjs) applies the exact-configuration and bidirectional fresh-ray macro *search predicates* to the frozen 663-machine list in `resources/BB6_holdouts_663_2026-10-16.txt`. Its self-tests pass on the four-step read-one lasso, Agent6's three-step entry-macro witness, and the F287 bounded negative example.

The completed CI screen [42306119782](https://github.com/FlareZ123/bb6/actions/runs/42306119782) used:
- entry prefix limit 10,000 (entry steps 0 through 9,999);
- blank-origin macro length at most 32;
- exact configuration repeat search through step 1,000.

Observed result over all 663 machines:

    exactLassoCount          0
    entryMacroCount          0
    haltedBeforeLimitCount   0
    hits                     []

This is a bounded empirical negative screen, not a proof that any machine is nonhalting or that no longer lasso/macro exists. It establishes that the current short exact-cycle and fresh-ray macro predicates do not directly resolve this historical holdout set at these limits. The next useful step for these roots is a stronger machine-specific invariant or a different certificate family, rather than simply increasing the same small limits without a concrete structural hypothesis.

### Integration with the authentic F287 root

[AuthenticLassoIntegration.lean](AuthenticLassoIntegration.lean) uses Agent4's existing authentic F287 + turn + two-step global audit and applies its `addCertificate` graft to the new read-one lasso cylinder at the same `DecidedBelow 2` bound. It preserves the existing F287 root and earlier certificates while adding the independently source-proved lasso family. The combined `authenticLassoAudit_exhaustive` and `authenticLassoAudit_conserves` theorems compile in the pinned upstream Cryptids / Lean 4.35.0-rc4 environment. Successful source verification: [CI 42305562265](https://github.com/FlareZ123/bb6/actions/runs/42305562265). The updated integration additionally proves that the lasso cylinder is disjoint from the F287 root (at B/0) and from the turn and two-step halt cylinders (at A/0). The exact sum of these four pairwise-disjoint source-certified cylinders is `1 + 2·25^9 + 25^10 = 102,996,826,171,876` complete tables. This is the mass of the four known cylinders, not a numeric evaluation of the noncomputable audit report. An attempted `#eval` of the combined `authenticLassoAudit.report` in [CI 42306317211](https://github.com/FlareZ123/bb6/actions/runs/42306317211) failed because the imported authentic F287 audit is noncomputable. The optional report-evaluation step and scratch file were removed. No numeric combined report is claimed; the source-checked exhaustive theorem, total-mass conservation, pairwise disjointness, and exact four-cylinder mass sum remain.

This graft is a proof-tree composition with an already established F287 result; it is not a new proof of the F287 root. Likewise, the exact lasso principle is prior art in Agent13's finite-tape work, and the finite-entry macro theorem is prior art in Agent6's work. The contribution here is the Agent8-semantic finite-support adapter, the strict read-one lasso witness, and their integration into Agent32's physical search and Agent4's authentic global audit.

**Verification boundary:** the global soundness and mass-conservation theorems are kernel checked. The 56.8% and 68.06656% exact numeric report pairs are interpreted Lean VM output, not yet separate kernel-proved cardinality equalities. The new methods do not resolve the 663 historical holdouts, establish a universal score upper bound, or determine BB(6).

## Prior art, next proof obligations, and BB(6) gap

Agent44's prior [directed-drift and zero-writer work](../agent44-drift-closure/README.md) already gives the 43.907809280% nonhalting union and source-checked individual certificate schemas. Agent42 independently counted a special normalized zero cycle. Agent8 constructed the 25-way source Cover contract; Agent4 proved disjoint frontier mass accounting and authentic-root integration. This investigation adds a disjoint short-halting union and a concrete fully source-checked adaptive global frontier applying existing sound oracles. It is under im-results because external novelty has not been established.

The remaining open sector retains genuine long-halting and possible nonhalting machines, including the historical undecided roots. No complete universal upper bound, exact champion runtime, or exhaustive global closure exists. Closing BB(6) requires a finished all-table certificate with a proved attained score in the standard step semantics.

**Next:** investigate stronger machine-specific certificates for the 663 historical roots and the residual physical-trace open leaves; consider a kernel-checked proof of the depth-four numeric report; and connect any new certificates to authentic unresolved six-state roots. Do not treat the bounded negative screen or an open leaf as a halting/nonhalting verdict. Avoid treating a hypothetical read-zero graph path after write-one reversal as a real blank-tape orbit.
