# Global raw-table frontier from the first read-zero control path

**Current status:** original-source Lean-verified certified-or-open partial frontier, plus an exact combinatorial and exhaustive-computational count of **52.786874368%** of raw six-state/two-symbol tables with a sound short-halt or nonhalt certificate. This is intermediate infrastructure. BB(6) remains unresolved. Agent44 previously established the entire nonhalting portion, so no novelty claim is made for it.

## Mathematical statement

Adopt Agent8's source formalization: a machine has 12 input rows, each with 25 possible actions (one halt, 12 write-zero ordinary moves, 12 write-one ordinary moves); an unassigned sparse input is distinct from an actual halt. Every run starts on a two-way all-zero tape in state A. Its Busy Beaver score includes the final attempted halting instruction.

Starting at A, follow the six read-zero control rows until their first halt or first repeated state. Record two separate sufficient properties of the successful transitions: (Z) every action writes zero, preserving a physically blank tape even if directions change; (D) every action moves in one fixed direction, preserving a fresh blank ray even if the machine writes ones. If Z **or** D holds through the first repeated control state, the actual blank-start machine never halts. If Z **or** D holds until a first encountered halt, that halt is physically reached, after at most five successful moves, and has exact step score k between one and six. All other cases remain unclassified by this argument. In particular, following read-zero transitions after a write-one and a reversal is only an enumeration choice; it is **not** treated as a valid machine simulation without a separate physical source certificate.

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

The percentage is a conservative, rigorously reasoned table classification. It does not provide a universal score upper bound or the number of rooted hard holdouts.

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

## Actual source-proof-carrying frontier

[ZeroPathAudit.lean](ZeroPathAudit.lean) defines the narrower global sparse frontier that follows known zero-writing actions only. Its first-free-input scanner is formally sound, and the raw-table frontier is exhausted by certified or explicitly open cases. [Source CI 42290328171](https://github.com/FlareZ123/bb6/actions/runs/42290328171) checked standard-only Lean axioms and computed the executable report:

    certified 14,857,432,861,328,125
    open      44,747,211,914,062,500.

[ControlPathAudit.lean](ControlPathAudit.lean) improves this to a global original-machine partial frontier incorporating three sound preexisting proof schemas: finite halting, arbitrary-direction zero-writer closure, and fixed-direction blank-ray closure. The scanner can follow a hypothetical read-zero control path after any assigned action, but it never infers halting or nonhalting from that hypothetical path. Each certified leaf is created only through Agent8/44's source-sound Boolean oracle. All other leaves are marked open.

Formally compiled theorems include scanControlPath_sound, directionalMaskOracle_sound, controlDecisionOracle_sound, globalControlPathAudit_exhaustive, and globalControlPathAudit_conserves, the last asserting certified mass plus open mass equals **exactly 25^12**. All passed full unmodified-source Lean 4.36.0-rc2 CI [42291051949](https://github.com/FlareZ123/bb6/actions/runs/42291051949), with only standard Lean axiom dependencies and no sorryAx. The globally exhaustive but **partial** Lean search tree is a real source proof object, not a search log.

**Verification boundary:** This exact 52.786874368% comes from a mathematical bijective count plus exhaustive C++ computation of a guaranteed decidable subfamily. [ControlPathMassEval.lean](ControlPathMassEval.lean) separately evaluates the Lean audit's *own* exact certified/open mass, which may be larger because the sound finite halting oracle detects additional cases. Until that evaluation is inspected and its relation to the closed count audited, 52.786874368% must not be claimed as the audit report's exact output or a kernel-checked cardinality theorem. Source-level soundness and total mass conservation are already kernel-checked.

## Prior art, next proof obligations, and BB(6) gap

Agent44's prior [directed-drift and zero-writer work](../agent44-drift-closure/README.md) already gives the 43.907809280% nonhalting union and source-checked individual certificate schemas. Agent42 independently counted a special normalized zero cycle. Agent8 constructed the 25-way source Cover contract; Agent4 proved disjoint frontier mass accounting and authentic-root integration. This investigation adds a disjoint short-halting union and a concrete fully source-checked adaptive global frontier applying existing sound oracles. It is under im-results because external novelty has not been established.

The hard sector retains genuine long-halting and possible nonhalting machines, including the historical undecided roots. No complete universal upper bound, exact champion runtime, or exhaustive global closure exists. Closing BB(6) requires a finished all-table certificate with a proved attained score in the standard step semantics.

**Next:** obtain a source-audited numeric report for the combined audit, investigate finite-prefix clean-ray entry or formally checked lasso leaves that expand genuine original-machine coverage, and connect the surviving sparse search to nontrivial rooted six-state machines. Avoid treating a hypothetical read-zero graph path after write-one reversal as a real blank-tape orbit.
