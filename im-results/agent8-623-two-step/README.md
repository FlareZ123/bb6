# Cryptids #623: sharp B-drain envelopes and paired terminal-gate restrictions

**Research status:** BB(6) remains open. The results here constrain all accelerated #623 section transitions and every hypothetical terminal event of its actual blank-root run. They do not establish a globally surviving orbit. This directory is intermediate research, deliberately kept under `im-results/` rather than `results/`.

## Source boundary

The machine is the original Cryptids `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`. All theorem source files import DeepMind's original module `BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA`, pinned to upstream commit `c86f15861709b76042998c5211c7b2f83991621b`. The exact accelerated section state is `D(a,d)`, with genuine blank-origin starting point `D(0,7)`. The upstream source's `evalA`, `drainB`, `highLevelNext`, `run`, and machine-to-section equivalence are imported intact.

The single manually triggered [Lean source audit](../../.github/workflows/agent8-623-third-affine.yml) compiles all dependencies in upstream's pinned Cryptids checkout, using Lean 4.35.0-rc4. Source-matched local proofs were additionally tested with Lean 4.36.0-rc2. Source-authenticated historical gates and parity are in [Agent49ParitySource.lean](../agent49-parity623/Parity623Source.lean).

## Sharp all-input drain region

If the source evaluator successfully drains `B(a,b,d) = D(A,D)`, the following inequalities hold for **every** natural-number input:

```text
a <= A + b
d + 3*b <= D <= d + 7*b
```

The lower bound on third-counter growth is imported from [TernaryBudgetSource.lean](../agent8-623-inverse/TernaryBudgetSource.lean). Our new source results prove the exact first-loss coefficient `1` and third-growth coefficient `7`, through these reusable evaluator potentials:

```text
evalA(a,k,m) = (A,B,D)  =>  a+B <= A+k+1
evalA(a,k,m) = (A,B,D)  =>  D+2*B <= m+2*k+3
```

See [DrainFirstSharpSource.lean](../agent8-623-inverse/DrainFirstSharpSource.lean) and [DrainSevenSource.lean](../agent8-623-inverse/DrainSevenSource.lean). Both coefficients are optimal: for `a>=1,b=1` the source gives `B(a,1,d)=D(a-1,d+7)`. The earlier [GateRepulsionSource.lean](../agent8-623-inverse/GateRepulsionSource.lean) also gives the upper first-output estimate `A<=a+k` whenever `b<3^k`.

A direct consequence is the **safe input cone**:

```text
B(a,b,d)=D(A,D) and 2*d+15*b+8 <= a
    => 2*D+8 <= A.
```

The latter output cone has an independently proven unconditional next accelerated return, so the source cannot terminate in the next section step.

## Five source-branch gate budgets

The exhaustive positive-even-first-coordinate branches are divided according to the second coordinate's parity and which side of the diagonal is occupied. The predicate `gateBudget a d k` is a disjunction of five *sufficient* arithmetic estimates, each requiring an explicit `3^k` size bound and a linear room inequality.

[GateCompleteSource.lean](../agent8-623-inverse/GateCompleteSource.lean) proves that for every `a>0`, even `a`, and every successful source transition `T(D(a,d)) = D(A,D)`:

```text
gateBudget(a,d,k) => 2*A+8 <= D
                   => T(D(A,D)) succeeds.
```

This is an all-input, unbounded statement. It imposes no assertion that a genuine orbit remains in `gateBudget`.

## Four infinite safe outer sectors

Using both sharp drain coefficients, [FarSectorSource.lean](../agent8-623-inverse/FarSectorSource.lean) proves that a **successful** first transition has a successful immediate successor for each of the following positive-first-counter input sectors:

| Second counter parity | Strong first dominance | Strong second dominance (first counter even) |
| --- | --- | --- |
| `d % 2 = 1` | `a >= 16*d + 68` | `d >= 16*a` |
| `d % 2 = 0` | `a >= 16*d + 44` | `d >= 14*a + 24` |

The return moves into the far-left safe output cone. The first transition must succeed; the source theorem does not assert universal absence of first-step halting in these sectors.

## Consequences for the authentic blank-root run

The source supplies `run 0 = D(0,7)`, a parity proof `a % 2 = 0` for every surviving `run n`, and mass growth `7*(n+1) <= a+d`. The exact first five visits are:

```text
n : 0       1       2       3        4
    (0,7)   (6,14)  (6,31)  (26,26)  (2,83)
```

[ZeroTailSource.lean](../agent8-623-inverse/ZeroTailSource.lean) establishes exact input formulas `T(D(0,d))=D(d,7)` for even `d` and `D(d-1,14)` for odd `d`. Every `D(0,d)` with `d>=40` is consequently two-step safe. Combining this with the source's mass-growth lemma and the explicit finite initial visits rules out a zero-first-counter parent of a terminal daughter at **every** genuine section index, even if a return to zero occurs later.

[ParentCorridorSource.lean](../agent8-623-inverse/ParentCorridorSource.lean), [RootCorridorSource.lean](../agent8-623-inverse/RootCorridorSource.lean), and [HaltParentSource.lean](../agent8-623-inverse/HaltParentSource.lean) combine the budget and outer-sector exclusions. If an authentic section `D(a,d)` halts, it has an actual preceding visit `D(p,q)`, where `p>0`, satisfying:

```text
if q odd:   q < 16*p and p < 16*q+68
if q even:  q < 14*p+24 and p < 16*q+44
for every k: not gateBudget(p,q,k)
```

The terminal section itself satisfies the independently established power-of-three fatal gate:

```text
3^(d-a-5) <= 2*(a+d)+5
3^(a-d-5) <= 2*(a+d)+5
```

The [MachineHaltSource.lean](../agent8-623-inverse/MachineHaltSource.lean) wrapper transports this paired necessary condition directly to the original six-state machine using upstream's already proved machine-to-section equivalence.

**Verification distinction:** [source run 42344165418](https://github.com/FlareZ123/bb6/actions/runs/42344165418) verified the five-branch theorem. [Source run 42345112992](https://github.com/FlareZ123/bb6/actions/runs/42345112992) verified the sharp drain and four-sector statements. Rooted paired-witness and machine-level wrapper proof files are currently subject to the next original-source CI audit; local Lean compilation used source-matched definitions and explicit locally mocked imported proof interfaces. A CI failure due to a missing imported `.olean` was resolved by compiling the module as an importable object, with no changes to theorem hypotheses.

## Quantified limitation and research direction

The independent [finite coverage diagnostic](coverage.py) mirrored the exact accelerated recursion for the first 5,000 section visits and categorized them, in priority order:

| Branch | Visits |
| --- | ---: |
| Five gate budgets | 1,924 |
| Strong first-dominance sector | 232 |
| Strong second-dominance sector | 433 |
| Zero-first-coordinate case | 1 |
| **Outside all current two-step safety certificates** | **2,410** |

These finite observations are computational diagnostics, with explicit assertions in the script. They demonstrate substantial uncovered territory and cannot support an all-time BB(6) conclusion. The first genuinely useful next proof target is a root-specific invariant or symbolic multi-step return theorem covering those excursions outside the gate and both outer sectors. Further local constant refinements alone are unlikely to decide #623.

The current exact value of BB(6) remains undetermined.
