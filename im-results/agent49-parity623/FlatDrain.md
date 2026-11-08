# Exact one-level ternary drain and a bounded Cantor failure language for #623

**Agent 49, 8 November 2026.** This is an intermediate arithmetic advance for the original six-state Cryptids machine #623, `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`. It is neither a decision of the authentic blank-root orbit nor a determination of BB(6). The original accelerated machine is pinned to `google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b`.

## Complete nested-recursion elimination

Write `B(a,b,d)` for the original upstream `drainB`, returning either `none` or `D(A,D)`. Its nested evaluator can be eliminated **exactly for every natural input**, including failing cases:

| Input | Exact identity |
| --- | --- |
| `b=0` | `B(a,0,d)=some(D(a,d))` |
| `b=3q`, `q>0` | `B(a,3q,d)=B(a+1,q-1,d+6q+3)` |
| `b=3q+1`, `a>0` | `B(a,3q+1,d)=B(a-1,q,d+6q+7)` |
| `b=3q+1`, `a=0` | `B(0,3q+1,d)=none` |
| `b=3q+2`, `a>0` | `B(a,3q+2,d)=B(a-1,q+1,d+6q+5)` |
| `b=3q+2`, `a=0` | `B(0,3q+2,d)=B(0,q,d+6q+7)` |

Every recursive right-hand block count is strictly less than the input `b`. Thus the separate executable `flatB` has a finite chain with only constant-work ternary cases per round. Its original-source identity `flatB_eq_drainB` establishes exact equality of *complete outputs*, not merely the halting predicate. The interpreter makes at most logarithmically many recursive calls; its bit complexity additionally depends on the sizes of the arithmetic operands. It does not bypass the unbounded root-orbit question.

## Exact bounded failure classification

Define an arithmetic predicate without machine evaluation:

```
bad(0,b)     iff b=1
bad(a+1,b)   iff (b mod 3=1 and bad(a, floor(b/3)))
                  or (b mod 3=2 and bad(a, floor(b/3)+1)).
```

The theorem `drain_none_iff_bad` establishes, for **every** `a,b,d ∈ ℕ` with `b≤3^a`,

```
B(a,b,d)=none  iff  bad(a,b).
```

This is a complete quantified decision criterion on an exponentially expanding rectangle of inputs. The underlying source-safe ternary-ones budget is used only for the `b≡0 mod 3` branch.

For each `a≥1`, the failed block counts strictly below `3^a` form the finite set

```
F_a = { (3^a+1)/2 + 2*sum(e_j*3^j, j=0..a-2) :
        each e_j is 0 or 1 }.
```

Hence **exactly `2^(a-1)` of the `3^a` block counts fail**, independently of `d`. The first sets are `F_1={2}`, `F_2={5,7}`, `F_3={14,16,20,22}`, `F_4={41,43,47,49,59,61,65,67}`.

The counting and closed-form statements are paper corollaries of the kernel-checked bounded predicate theorem; they are **not separately formalized as cardinality theorems**. Their elementary induction uses the exact recursion `F_(a+1)={3x-1,3x+1:x∈F_a}`, which follows because `bad(a,0)` and, for `a≥1`, `bad(a,3^a)` are false. The two child maps are injective with distinct residues modulo 3.

## Verification scope and frontier

- [Original-import proof module](FlatDrainSource.lean) derives the six identities, `flatB_eq_drainB`, and `drain_none_iff_bad` directly for the unchanged upstream `evalA` and `drainB`. A manual [source-pinned CI workflow](../../.github/workflows/agent49-623-flat-drain.yml) verifies the Lean theorems with an axiom audit. At first draft, source CI run [42525791738](https://github.com/FlareZ123/bb6/actions/runs/42525791738) was in progress; check its final result before claiming source certification.
- An independent self-contained local Lean 4.36.0-rc2 model using verbatim source arithmetic equations passed the whole proof without `sorry` or custom axioms; all seven final theorem audits listed only `[propext, Quot.sound]`.
- The nontrivial ternary identities were checked separately against a Python implementation on `a=0..7`, `q=0..199`, `d∈{0,11}`, with the `b=3q` case restricted to `q>0`. Exact bounded failure sets matched for `a=1..8`. Those tests corroborate the theorem but do not establish an infinite result by themselves.
- Earlier source results [TernaryShift](TERNARY-SHIFT.md) already established the sharp initial safe prefix `b≤(3^a-1)/2` and its first failure; the present theorem **extends from a first-failure boundary to a complete fractal failure classification over `b≤3^a`**, plus a new nested-recursion-free exact evaluator. Do not duplicate or misrepresent the earlier sharp prefix as new work.

**Unresolved quantifier:** The real blank-root state `D(0,7)` follows the infinite composition of the full high-level transition. No root-sensitive invariant has been proved that excludes its full `drainB` failures. The new local classification can speed exact inverse, residue, and gate investigations, but it gives no universal bound on the six-state halting time.
