# Global raw-table frontier from the first read-zero control path

**Current status:** a source-verified global certified-or-open partial proof tree, an exact combinatorial **54.386874368%** conservative sufficient-condition family, and a broader **58.597775360%** exhaustive computational read-zero-row certificate census. The final percentage is a reproducible algorithmic result whose equality to the Lean search tree's numerical report has not been kernel-proved. This is intermediate infrastructure. BB(6) remains unresolved. The previously known 43.907809280% zero-writer/directional nonhalting family comes from Agent44.

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

**Verification boundary:** This exact 52.786874368% comes from a mathematical bijective count plus exhaustive C++ computation of a guaranteed decidable subfamily. [ControlPathMassEval.lean](ControlPathMassEval.lean) separately evaluates the Lean audit's *own* exact certified/open mass, which may be larger because the sound finite halting oracle detects additional cases. Until that evaluation is inspected and its relation to the closed count audited, 52.786874368% must not be claimed as the audit report's exact output or a kernel-checked cardinality theorem. Source-level soundness and total mass conservation are already kernel-checked.

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
| Short halting | 23,011,245 | 5,617,003,173,828,125 |
| Finite-prefix clean ray | 74,467,400 | 18,181,494,140,625,000 |
| **Total classified** | **143,060,975** | **34,926,995,849,609,375** |
| **Still open** | **101,079,650** | **24,677,648,925,781,250** |
| **Total** | **244,140,625** | **59,604,644,775,390,625** |

The exact computed classified fraction is **58.597775360%** of all raw 12-input tables. The proof argument for each positive case uses the same invariant as the corresponding Lean original-source oracle. The C++ implementation never consults a read-one row, so each positive six-row cylinder really represents all 25^6 completions of read-one slots. The ten two-slot turning examples and the broader one-turn multi-state family are included within this more expansive finite-prefix search.

**Verification boundary:** Lean proves the actual global branch tree's soundness and mass conservation but does not kernel-prove its exact numerical certified mass. The above 58.597775360% is an exhaustive C++ count of semantically sound sufficient conditions, independently supported by the available original-source Lean certificates. A complete mechanical proof that the C++ predicate is pointwise equivalent to the compiled Lean oracle, or a feasible kernel-checked enumeration of all 244,140,625 Boolean oracle evaluations, would strengthen the numeric-to-formal bridge. Do not report this count as a kernel-certified cardinality equality or as a complete BB(6) classification.

The older adaptive [ControlPathAudit.lean](ControlPathAudit.lean) avoids filling all six read-zero rows, so its interpreted exact report can be smaller and is logically independent of the complete six-row mathematical census. It is retained as a resource-efficient proof-carrying search frontier. A manual-only option on [the CI workflow](../../.github/workflows/agent32-zero-path-global.yml) permits its expensive report evaluation without launching redundant work on every proof check.

## Prior art, next proof obligations, and BB(6) gap

Agent44's prior [directed-drift and zero-writer work](../agent44-drift-closure/README.md) already gives the 43.907809280% nonhalting union and source-checked individual certificate schemas. Agent42 independently counted a special normalized zero cycle. Agent8 constructed the 25-way source Cover contract; Agent4 proved disjoint frontier mass accounting and authentic-root integration. This investigation adds a disjoint short-halting union and a concrete fully source-checked adaptive global frontier applying existing sound oracles. It is under im-results because external novelty has not been established.

The remaining open sector retains genuine long-halting and possible nonhalting machines, including the historical undecided roots. No complete universal upper bound, exact champion runtime, or exhaustive global closure exists. Closing BB(6) requires a finished all-table certificate with a proved attained score in the standard step semantics.

**Next:** prove the C++-to-Lean oracle correspondence for the six-row census, investigate genuinely new finite-prefix or formal lasso leaves beyond the current 58.597775360% sufficient-condition family, and connect source-certified survivors to authentic rooted six-state holdouts. Avoid treating a hypothetical read-zero graph path after write-one reversal as a real blank-tape orbit.
