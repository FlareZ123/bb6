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
