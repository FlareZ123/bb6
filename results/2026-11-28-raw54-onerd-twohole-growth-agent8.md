# Raw54 E1=1RD: source-proved growing two-hole cylinder

**Status:** Original-source Lean 4.36.0-rc2 certified, [CI run 46153616459](https://github.com/FlareZ123/bb6/actions/runs/46153616459). The result is a **local 625-completion nonhalting theorem**, not a completed Raw54 parent Cover or a BB(6) upper bound.

## Theorem and scope

Consider the six-state two-symbol partial table (states A,B,C,D,E,F; blank 0; halting fill allowed in each unassigned instruction):

```text
A: 1RB  ---
B: 1RC  0RD
C: 0RD  1RF
D: 1LD  0LE
E: 1LB  1RD
F: 0RB  ---
```

Equivalently, `1RB---_1RC0RD_0RD1RF_1LD0LE_1LB1RD_0RB---`. For **every completion** of A1 and F1, the blank-tape run is infinite. This is a disjoint family of 25² = 625 ordinary completions of the Raw54 E1=1RD branch. In particular, all 625 satisfy `WeightedBound 1006` (vacuously in the nonhalting case).

The original-source theorems are `BB6.Agent8Raw54.TwoHoleGrowth.never` and `.cover` in [Raw54TwoHoleGrowth.lean](../im-results/agent8-raw54/Raw54TwoHoleGrowth.lean). The accepted CI run compiles the complete original dependency closure, checks the stated theorem axioms and exports a build log; the axiom profile of `.cover` is exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

## Explicit uniform infinite return

Represent a tape zipper by `Z0 = ⟨state, left, right⟩`, nearest cell first, with the scanned symbol the head of `left`. Write `0^j` for `j` zeros and `11` for two ones. Define the word `P=00011`. The blank tape enters in exactly **207 defined transitions** the state

```text
S(k) = ⟨B, [], 1 0^11 11 P^k 0 11⟩
```

at `k=0`. Every `S(k)` has a defined positive-time return to `S(k+1)`:

```text
run0 table (162 + 40*k) (S k) = some (S (k+1)).
```

This is a *universal theorem for every natural `k`*, not a finite simulation of selected values. The proof uses a second family

```text
T(k) = ⟨B, [], 1 0^3 11 0^7 11 P^k 0 11⟩
```

and exact uniform phases:

| Phase | Cost | Certificate |
| --- | ---: | --- |
| `S(k) → T(k)` | 15 | literal finite reduction |
| `T(k) → U(k)` | 41 | literal finite reduction |
| `U(k) → V(k)` | `13k` | arbitrary-tail right-sweep, `sweepR` |
| `V(k) → W(k)` | 94 | literal finite reduction |
| `W(k) → X(k)` | `27k` | arbitrary-tail left-sweep, `sweepL` |
| `X(k) → S(k+1)` | 12 | literal finite reduction |

The rightward pump replaces each `00011` block with a left transfer `01111` in exactly 13 steps; the leftward pump transfers each `01111` into `00011` on the right in exactly 27 steps. Both microstep lemmas quantify over **arbitrary untouched tape tails**; their inductions use the general source-proved `sweepR` and `sweepL` theorems, not enumeration. Arithmetic gives `15+41+13k+94+27k+12 = 162+40k`.

Since every epoch costs at least 162 defined transitions, the source-proved `never_of_growth` theorem gives `NeverHalts m` for every complete machine `m` compatible with the literal partial table. Thus both unknown instructions A1 and F1 remain irrelevant forever on the blank run, regardless of their completion.

## Reproducibility and integration limit

The proof is self-contained in the named Lean module except for reused original-source `Raw54OneRDBankAudit`, `SweepPumping`, and `never_of_growth` prerequisites. The workflow [agent8-raw54-twohole-growth.yml](../.github/workflows/agent8-raw54-twohole-growth.yml) uses Lean 4.36.0-rc2, rebuilds all imported modules from original source and audits `epoch`, `never` and `cover`. [Accepted run 46153616459](https://github.com/FlareZ123/bb6/actions/runs/46153616459) proves those exact exports.

This theorem resolves the last two-hole residual cylinder in the **discovery-level** Raw54 1RD residual roster after the 169-DFA bank and anchored-mutant candidates. It does not, by itself, source-accept the entire roster's composition or settle the still-open one-hole residuals. The broader Raw54 parent and Canonical38 BB(6) maximality proof remain open.
