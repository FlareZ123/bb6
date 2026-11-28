# Raw45: six unbounded growth cylinders from a shallow first-hole cut

## Mathematical claim and source boundary

The seven-hole Raw45 quotient representative is

```text
1RB---_1RC---_0RD---_1LD1RB_------_------
```

A depth-two first-missing-instruction classification (1000-step simulation cap,
32 predecessor checks for translated lassos, TNF first-use target cutoff)
has 15 split nodes, 159 translated-lasso leaves, 44 state-alias branches,
and 143 five-hole residuals. **Six** of the 143 residuals do not query
another hole or exhibit a recognized translated lasso by 1000 steps.
Those six are *not* undecidable by experiment: each admits a simple
all-depth positive-cost growing blank-tape section.

The six original-source Lean proof files in this directory are
**candidate** source proofs until the original-source CI and axiom gates
pass. They use `SweepPumping.run0`, finite exact primitive-step
identities, the source-proved arbitrary-length `sweepL` and `sweepR`,
and `never_of_growth`. They contain no admitted assertions or finite-run
extrapolation. **Do not count the 143 residuals as closed**: the other
137 cylinders still need complete certificates. No unconditional
Raw45 parent Cover or global BB(6) bound is claimed.

Let (0^k) and (1^k) mean k equal bits. In the source zipper
`Z0`, the **left** word includes the scanned cell, both words are
zero-padded, and the head state is D in all six phases.

| Residual | B1 | C1 | Initial phase `(D,L,[])` | Blank entry | `phase(n) → phase(n+1)` primitive cost | Proof |
|---|---|---|---|---:|---:|---|
| M1 | 0LD | 0RC | `0^(n+2) 1^(n+2)` | 3 | `2n+8` | [Raw45M1Growth.lean](Raw45M1Growth.lean) |
| M2 | 0RC | 0RC | `0^(2n+2) 11` | 3 | `4n+6` | [Raw45M2Growth.lean](Raw45M2Growth.lean) |
| M3 | 1LB | 0LD | `00 1^(3n+2)` | 3 | `12n+20` | [Raw45M3Growth.lean](Raw45M3Growth.lean) |
| M4 | 1LB | 0RC | `0^(3n+6) 1` | 15 | `6n+18` | [Raw45M4Growth.lean](Raw45M4Growth.lean) |
| M5 | 1LB | 1RC | `00 1^(3n+2)` | 3 | `6n+12` | [Raw45M5Growth.lean](Raw45M5Growth.lean) |
| M6 | 1RC | 0RC | `0^(n+2) 1^(n+2)` | 3 | `2n+6` | [Raw45M6Growth.lean](Raw45M6Growth.lean) |

The residuals are mutually disjoint by the B1/C1 rows and each has
five undefined transition rows. For any total completion compatible with
one of these tables, all positive-length epochs avoid *every* undefined
instruction. Upon source acceptance the six theorems will certify
`6 × 25^5 = 58,593,750` total six-state machines as nonhalting, in
six canonical first-use residual subcylinders. This is not six whole
seven-hole parents.

## Exact sweep mechanisms

M1 and M6 share the same phase but have different B1 transitions.
In both, D0 transfers `n+2` zeros leftward, writing ones, C1
transfers n scanned right ones into zeros on the left, and C1/C0
finishes at the next outer zero. M6 uses D1/B1 as a two-step turn;
M1 uses D1/B1/D1/B0 as a four-step turn.

M2 transfers `2n+2` zeros leftward through D0, carries a fixed
two-one left marker, then uses D1/B1 and `2n` repetitions of C1,
finishing in C1/C0. The resulting phase has two more zeros.

M3 and M5 begin with two D0 actions. D1 and `3n+3` B1 left
steps shuttle all ones to the right, followed by B0. In M3,
each of the `3n+3` return packets is C1/D1/B0, three
primitive steps writing a new left one, and the C1/D1/B0/C0
exit takes four steps. In M5 each return packet is a single
C1 step, with C1/C0 as the two-step exit. Both grow the
permanent one-run by three cells.

M4 has an exceptional first entry but thereafter uses the
stabilized phase `0^(3n+6) 1`, first seen after 15 real
steps. The D0 left sweep transfers `3n+6` zeros to the
right as ones; D1/B1/B1/B0 moves the leftmost marker;
`3n+6` C1 right steps erase the transferred ones;
C1/C0 supplies three further zeros.

Each finite packet identity in the corresponding source file has
arbitrary untouched left/right tails and can be checked by exact
`run0` reduction. Each unbounded repetition uses the
source-proved sweep induction. The original-source bridge
`never_of_growth` shows that an arbitrary compatible machine has
live runs of unbounded length; this is strictly stronger than
a 100,000-step empirical nonhalt.

## Reproduction and remaining work

The existing manual workflow
[agent38-m62-kernel.yml](../../.github/workflows/agent38-m62-kernel.yml)
has targets `raw45-m1` through `raw45-m6`, preserving the shared
original-source `unpack.py` and `tools/lean_compile_closure.py`
path with an axiom audit. First source runs:

- M6 [46089633917](https://github.com/FlareZ123/bb6/actions/runs/46089633917)
- M1 [46089741048](https://github.com/FlareZ123/bb6/actions/runs/46089741048)
- M2 [46089744374](https://github.com/FlareZ123/bb6/actions/runs/46089744374)
- M5 [46089846445](https://github.com/FlareZ123/bb6/actions/runs/46089846445)
- M3 [46089959353](https://github.com/FlareZ123/bb6/actions/runs/46089959353)
- M4 [46089962824](https://github.com/FlareZ123/bb6/actions/runs/46089962824)

At initial submission these runs are queued, **not accepted**.
The local shell and Python failed with a runtime `ClientError`
before any command executed; this is not a Lean compile diagnostic.
The next step is to repair actual compiler messages, certify all
six exact original-source proofs, and incorporate them by literal
table identity into a source-sound Raw45 first-hole partition. The
remaining 137 shallow residuals still require separate work; a
full parent Cover must combine all descendants at the common
champion threshold and the exact canonical membership theorem.


## A complete mathematical recurrence for a different one-hole Raw45 branch

The more distant Raw45 subbranch `B1=0LA, A1=0LC` has literal
five-hole parent
`1RB0LC_1RC0LA_0RD---_1LD1RB_------_------`.
A 120/900-step translated-lasso and width-at-most-5 sparse n-gram
depth-first first-hole enumerator yields 11,449 visited nodes,
477 splits, 8,834 lasso leaves, 68 n-gram-closed leaves, 2,068
last-hole leaves, and only **two** live one-hole residuals,
which exchange E and F. These are experimental classifier counts,
**not** an original-source accepted enumeration yet. The source
generator's capacity was not exhausted in this run. The maximum
remaining first-hole query was at step 95.

The first one-hole residual is

```text
1RB0LC_1RC0LA_0RD1RE_1LD1RB_1LF---_0LA0LF
```

The second residual is its state-E/F conjugate:

```text
1RB0LC_1RC0LA_0RD1RF_1LD1RB_0LA0LE_1LE---
```

Write `P=001`, `B=010`, `I=011`, `Q=101`,
`C=0000`, `U=000`, and `V=00001`. In the
source-zipper convention (left includes the scanned cell),
define two sections, with head in E and left word `01`:

- `odd(n)` has right word `P^(n+1) B 1^(n+1)`
- `even(n)` has right word `P^(n+1) C 1^(n+2)`

The blank run enters `odd(0)` after 45 transitions. Exact
primitive transition identities with arbitrary untouched tails
are the four-step E0 frontier turn
`(E,01,R)→(B,01,01R)`, the three-step
`(B,0L,010R)→(B,0101L,R)`, the two-step odd
right-end `(B,0L,10R)→(E,011L,R)`,
the eight-step even right-end
`(B,01L,000R)→(E,01L,010R)`, the seven-step
`(E,0111011L,R)→(E,01L,00001R)`,
and the five-step
`(E,01011L,R)→(E,01L,001R)`.

Three elementary word inductions enable the two arbitrary-length
sweeps:

```text
01 P^m B = B^(m+1) 10
01 P^m C = B^(m+1) 000
Q^m 1    = 1 I^m
```

The first identity converts the odd right frontier to `B` packets;
the second does the same for the even frontier. The third rotates
the left `Q` packets to `I` packets, which return as `P`
packets under five-step `E0` sweeps. The seven-step odd turn
changes the right suffix `10` to `00001`,
whereas the eight-step even turn changes `000` to `010`.

Therefore the **exact quantified recurrences** are

```text
odd(n)  -> even(n)  in 8n+24 primitive steps
even(n) -> odd(n+1) in 8n+28 primitive steps
odd(n)  -> odd(n+1) in 16n+52 primitive steps
```

All epochs have positive duration. Thus every total completion
of the one-hole literal residual avoids its hole indefinitely
and is nonhalting; its E/F conjugate is likewise nonhalting.
This is presently **mathematical candidate + original-source Lean
proof pending gate**, not yet an accepted child Cover.
Source: [Raw45B1LA_A1LC_L1Growth.lean](Raw45B1LA_A1LC_L1Growth.lean),
[CI 46090746169](https://github.com/FlareZ123/bb6/actions/runs/46090746169).

One complete source-sound proof of the five-hole branch requires
reconstructing and checking the finite lasso/ngram decision tree
and the conjugacy. The two outliers are not grounds for treating
the other branches as solved without that tree.


## Full five-hole child certificate candidate

The first-hole tree has now been materialized as
[Raw45B1LA_A1LC_FullCut.lean](Raw45B1LA_A1LC_FullCut.lean)
(267 KB). It is a single **source-checkable exact upper-bound
candidate** for all completions of
`1RB0LC_1RC0LA_0RD---_1LD1RB_------_------`,
at weighted threshold **101** (root queries C1 at ordinary
step 8, and maximum further hole query step 95). The tree has
11,449 nodes including root, 477 split nodes including root,
8,834 translated-cycle leaves, 2,068 last-hole leaves,
68 two-sided local-window certificates (38 of width 1,
14 of width 3, 16 of width 4), and precisely the
two state-conjugate one-hole exceptions proved by the
alternating macro recurrence above.

The 68 explicit local-window proof objects and exact literal
source machines are recorded in
[Raw45B1LA_A1LC_NGram68.lean](Raw45B1LA_A1LC_NGram68.lean),
generated using the existing source-accepted
`NGramCertificate` checker. Unlike the discovery
ngram closures, the source file has theorem statements
`check p_i c_i = true` proven by kernel reduction and quantified
`NeverHalts` lifts. Acceptance is pending the bank's original-source
Lean gate; the *candidate* is not a certified upper bound until the
entire audit, including all 8,834 translated-cycle checks,
the 68 n-gram checkers, and both exceptional induction proofs,
is accepted.

The full-cut source uses the existing `ZipThreeHoleAudit`
`Audit` datatype, constructs 24 first-level C1 children,
and reduces each using `zipCheck 96` plus the source
`certifiedZip` soundness theorem. It does not introduce a
trusted external oracle or alter the checker.

Focused CI links:
[ngram bank](https://github.com/FlareZ123/bb6/actions/runs/46091283707)
and [full cut search](https://github.com/FlareZ123/bb6/actions/workflows/agent38-m62-kernel.yml).
A successful full-cut original-source gate would certify all
`25^5=9,765,625` physical completions of this exact five-hole
Raw45 child at weighted score at most 96.


## Exact 96-step halting attainment witness

The complete-discovery first-hole tree has exact *weighted* maximum
**96** (not the initial conservative 101). Re-running the six-state
simple incoming-zero-path delay automaton used by
`possibleDelays` on every one of the **2,545** first-hole
nodes returned maximum `n+1+d=96` for exactly two
literal leaves, both with `n=95` and `d=0`.
All other discovery scores were ≤75. Thus 96 is the natural
candidate **exact** weighted maximum for the entire five-hole child,
*conditional* on source acceptance of the 11,449-node upper audit.
The literal attainment witnesses (genuine E1/F1 halting rows) are:

```text
1RB0LC_1RC0LA_0RD0LE_1LD1RB_0LF---_1RF0RA
1RB0LC_1RC0LA_0RD0LF_1LD1RB_1RE0RA_0LE---
```

The first total machine is provided in source Lean at
[Raw45Sharp96Witness.lean](Raw45Sharp96Witness.lean).
It proves an *actual* blank-run `HaltsAfter witness 95`,
initial blank delay zero, and
`¬ WeightedBound 95 witness` via exact `run` computation.
This is independent of the hard-growth and ngram subproofs.
Its original-source Lean+axiom gate is
[manual CI](https://github.com/FlareZ123/bb6/actions/workflows/agent38-m62-kernel.yml)
target `raw45-sharp96`; do not claim accepted lower bound
until the run succeeds.

The full-cut source has been sharpened everywhere to
`zipCheck 96` and `WeightedBound 96`
(commit 545c9c72); kid04 smoke source was also sharpened to 96.
The exact 96 lower and full 96 upper, once source accepted,
will make a locally exact five-hole quotient subfamily bound.
