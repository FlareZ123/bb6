# F197: exact four-phase macro reduction (Raw132)

Archived holdout literal: `1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF`.
Only C1 is undefined. Raw132 is the retained prefix A0=1RB, B0=1RC, C0=0RD, D0=0RE. Agent2 has produced a reproducible guarded [blank-root self-embedding candidate](../agent2-f197-sweep/NonhaltingCertificate.md). The original partial-table transport below supplies the conditional bridge to all compatible machines. The full source-connected root theorem and Cover remain unaccepted.

## Strongest reset families

[MixedCarry.md](MixedCarry.md) proves exact live returns for arbitrary interleavings of AT, TT, P=AAT, Q=TAT and AAA/TAA terminal, with arbitrary aligned left tail and exact cost 74+68m+14t. TTJ-carried form costs 209+68m+14t. The complete original-source import passed [CI 46084690743](https://github.com/FlareZ123/bb6/actions/runs/46084690743).

[MarkerMixed.md](MarkerMixed.md) extends the arbitrary mixed prefixes to two-P/J descent and provides a generic wrapping theorem for aligned right-tail-parametric base routines. [EpochCycle.md](EpochCycle.md) gives an unbounded cycle consuming four repeated R=AATAAAT blocks while producing 18 leading P blocks, cost 2448*n+26828, and a generic word-level certificate checker for arbitrary mixed-reset compositions. The new marker and cycle modules passed local Lean with standard axioms against the literal source slice; complete import checks are pending. These families are finite exact transformations. Agent2's guarded self-embedding and root reach computation now address the changing deep tail; the remaining obligation is the complete original-source Lean proof of the root and loop, then the weighted Cover consumer.

## Literal macro semantics

All stack words are nearest-first with implicit infinite zero tails. At phase D, L excludes the head and R includes it. At B/F/A, L includes the head and R excludes it. A rule deletes its input prefixes and prepends output prefixes to the unchanged suffixes. The blank orbit enters D(011,empty) after three live steps.

| Phase | L in | R in | L out | R out | Next | Live steps |
|---|---|---|---|---|---|---:|
| D | ε | 01 | 01 | ε | D | 4 |
| D | ε | 111 | 010 | ε | D | 5 |
| D | ε | 1000 | 0110 | ε | D | 4 |
| D | 0 | 110 | 01 | 01 | D | 9 |
| D | ε | 101 | 01 | 0 | D | 6 |
| D | 0 | 00 | ε | 001 | B | 6 |
| B | 0 | 0 | 01 | ε | D | 2 |
| B | 11 | ε | ε | 00 | B | 2 |
| B | 10 | ε | ε | 10 | F | 2 |
| F | 1 | ε | ε | 1 | F | 1 |
| F | 0 | ε | ε | 1 | A | 1 |
| A | 0 | 1 | ε | 00 | B | 3 |
| A | 1 | 1 | 01 | ε | D | 4 |

The phase constraints D:L starts 0, B:R starts 0, A:R starts 1, F:unrestricted are preserved by every successful rule. They make the rules exhaustive except the fatal D R=1001 prefix, which reaches C1 after three ordinary transitions and returns none on the fourth query. All successful rules have positive costs. Therefore the macro orbit terminates iff the literal machine halts.

`Macro.lean` is standalone Lean 4.36.0-rc2, no external imports; local compile passed, `#print axioms F197.halt_iff_macro_halt` reported [propext, Quot.sound]. It formalizes literal-table semantics via two infinite Boolean streams, checks arbitrary suffixes, proves phase validity and exact macro-vs-primitive halting equivalence. `CoverBridge.lean` now proves that every successful literal stream step and finite run lifts to the original integer-tape semantics for **every** compatible total machine. The relation identifies tape cells head−(n+1) and head+n with the left and right streams. Since the successful stream steps never query C1, its assignment is unrestricted. `F197.CoverBridge.never_of_stream_live` takes all-time stream liveness from the true blank state and yields `BB6Coverage.NeverHalts m` for every compatible machine (25 completions). Local Lean 4.36.0-rc2 compilation against the exact relevant definitions of Macro and Frontier passed, with axioms `propext` and `Quot.sound` only. Full original module import and the fixed-score Cover consumer remain required.

## Historical finite-abstraction attempts

A finite run of 500,000 macro steps did not halt. Symmetric bounded ngram/rungram/periodic/lag primitive and macro abstractions failed to close. No conclusion from negative searches. Avoid simply extending these scans. The previous target was a phase-dependent grammar or sweep invariant eliminating the fatal prefix; the newer guarded self-embedding route supersedes this search. In samples D left starts 01, has internal zero runs of length at most two, and D00 reversal starts with a one-run of length 1 or 2. Right internal zero runs usually have length 1 or 3, with temporary leading exceptions caused by D110. Those are observations only. A useful analysis is D111/01/1000/101 as right sweep and B/F/A as left sweep, with D110 followed immediately by D01. Need relational constraints across sweep directions, rather than merely finite prefix windows.
