# Raw13 coupled-six-hole literal proof expansion (2026-11-27)

## Scope and strength

This is an intermediate coverage dossier, not a claim of the value of BB(6), a global reduction, or an accepted complete parent. Agent46 continued the existing Raw13 cut, targeting exact literal residual partial tables after FAR and BiDFA filters. The compatible-completion statements are machine-level `NeverHalts` theorems. All 121 new literal proof instances were individually checked locally using Lean 4.36.0-rc2 with recovered accepted checker dependencies, standard axioms only. The generated parent modules and full remote source closure have not been accepted in this invocation.

## New proof banks

| Family | New leaves | Source / fixture |
|---|---:|---|
| 0RB affine | 8 | Raw13Coupled6RBPumps.lean, coupled6-0RB-pumps.json |
| 0RB alternating binary phases | 3 | Raw13Coupled6RBTriple.lean |
| 0RB constant-cost insertion | 2 | Raw13Coupled6RBDrifts.lean, coupled6-0RB-drifts.json |
| Other affine | 74 | coupled6-extra-auto.json, emitGrowthBank.py |
| Left-oriented binary | 1 | Agent46OpenLeftSweep.lean, Agent46CounterLeftCheck.lean, coupled6-extra-counter.json |
| Pair-spaced binary | 5 | Raw13Coupled6PairCounter.lean, Raw13Coupled6PairCounter4.lean |
| Finite radix | 2 | Agent46RadixCheck.lean, coupled6-extra-radix.json |
| Movable radix-four marker | 6 | Agent46MarkerCheck.lean, coupled6-extra-marker.json |
| Finite terminal alphabet | 1 | Agent46TerminalCheck.lean, coupled6-extra-terminal.json |
| Sweeping marker | 2 | Agent46SweepMarkerCheck.lean, coupled6-extra-sweepmarker.json |
| Nonlinear two-count sweeps | 7 | Agent46UnarySweepCheck.lean, coupled6-extra-unary.json |
| Fixed-prefix terminal counters | 10 | Agent46PrefixTerminalCheck.lean, coupled6-extra-prefixterminal.json |
| **Total** | **121** | |

The original 0RB literal residual bank had 18 entries: 13 new and five inherited. The other initial unresolved set had 150 literal entries after subtracting prior BiDFA and manual certificates; 108 were proved in the earlier bank; the separately checked mirrored-counter theorem below adds one local proof (41 remain before later unpublished or unaccepted work). The generator consumes by exact table match. The 103 entries in its new JSON banks are distinct; five pair-counter leaves and thirteen 0RB leaves are additional source modules.

## Mathematical mechanisms

- Alternating binary phases: `root(7,n) -> root(10,n) -> root(7,n+1)` at positive cost. Arbitrary-width fill is proved by induction, using arbitrary protected suffixes.
- Variable-spacing paired digits: two digits in 3 or 4 cells. The carry removes a maximal pair, accumulates a unary transfer count, then restores the frame.
- Radix and terminal: little-endian digit words; decompose at the first non-maximal digit or the terminal symbol, prove zero-prefix and arbitrary positive carry cases. Terminal overflow may append a fixed word of ordinary digits.
- Marker: arbitrary digits followed by a distinguished marked digit and a zero suffix. Overflow recreates or moves the marker. The sweeping-marker variant allows either a marked or an unmarked tail and maintains nonempty ordinary digits.
- Nonlinear two-count sweep: for P=01, right tape P(PP)^i11P^j tail; j>0 gives (i+1,j-1), j=0 gives (0,2i+3) and toggles the tail. Two independent repetition parameters avoid fitting an invalid one-variable affine model.
- Fixed prefix: high digits of 8 cells with independent finite terminal alphabet, preserving fixed prefix. One variant has different terminal overflow.

## Next actual source consumption

Use existing workflow `agent46-raw13-cut.yml`, target coupled6Sibling, one or two moves per dispatch. 0RB, 1LA and 1LF have complete literal certificate inventories. Begin with those, then obtain actual accepted source artifacts and graft them. Current source generator is `generateCoupled6Sibling.py`; it rejects incomplete inventories deliberately. Do not count coverage by literal proofs until actual parent integration succeeds. The preceding incarnation could not dispatch. In the current continuation, source-pinned runs [46036860150](https://github.com/FlareZ123/bb6/actions/runs/46036860150) (0RB,1LA) and [46036872633](https://github.com/FlareZ123/bb6/actions/runs/46036872633) (1LF) generated complete literal inventories but failed before Lean on an ambiguous `FastBiDFA` import. The generated `Cert` API is the Raw59 rowwise checker, not Raw42's incompatible `FastCert`; the existing manual workflow now uses an explicit Raw59 override for `coupled6Sibling`. The repaired workflow subsequently passed for both 0RB and 1LA in [46037817669](https://github.com/FlareZ123/bb6/actions/runs/46037817669), artifact 15220979453, exposing both sibling `bound` theorems at 62123 with empty complements. The follow-up 1LF run 46037570445 was cancelled; no acceptance for 1LF is claimed.

## Pending growing-prefix theorem

`Agent46OpenSweep2.lean` and `Agent46GrowRadixCheck.lean` are kernel-checked general theorems. `discoverGrowRadix.py` regenerates seven concrete candidate banks and Lean modules. They have a unary prefix 010^(n+1), delimiter 10, radix-four digit words, binary terminal; a return increments n and the digit counter. Every one of the 70 symbolic macro searches succeeded locally. Source check 46038618203 failed at the finite Boolean terminal obligations because `checkClosed` was not unfolded for decidability. The emitter now splits the Boolean cases and unfolds the predicate explicitly. The seven remain uncounted pending source acceptance. Run the generated modules in CI or separate the finite checker obligations into named lemmas. Do not rediscover the macros.

Other pending: a 32-cell affine growth certificate had a long local check timeout. Four fixed-prefix overflow variants (tables beginning 1RB1LD1RC1RE/0LE/1RB with D0=0RF and E1=1RA) have exponential final-overflow costs, not a single affine carry; their normal carry and terminal advance traces work. Investigate a nested overflow induction. The mirrored binary-counter leaf `1RB1LD1RC1RE1LA1RE1LC0LA0RF1RA---0RB` has an exact exponential return at cost 52·2^k+4, now locally kernel-checked with standard axioms against recovered accepted repository proof objects. See [the mathematical dossier](Raw13Coupled6MirroredCounter.md) and source-pinned run [46037473169](https://github.com/FlareZ123/bb6/actions/runs/46037473169). The first source run failed on list normalization; that failure is repaired locally and the literal generator now consumes the theorem. The previous incarnation subsequently obtained a successful mirror source run 46038209365 (artifact 15217878031), discovered after dispatching the current repaired source run 46053983188. Unary recursion also passed source run 46038775729 (artifact 15219112456), and its exact literal has now been added to the sibling generator. The four phased-counter fixtures still await a successful source check; the generic PhaseCounter checker now compiles locally after separating structure fields. No claims are made about the other unresolved machines.

All material remains in im-results, since global source acceptance and meaningful coverage reduction are still outstanding.
