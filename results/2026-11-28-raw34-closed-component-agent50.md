# An exact closed C–D component proving 64 Raw34 six-hole cylinders never halt

**Status: unconditional all-completion Lean theorem, original-source accepted.** This result is an exact infinite-computation theorem about a structured class of six-state machines, not a global BB(6) upper bound.

## Statement

The canonical Raw34 parent fixes A0=1RB, B0=1RC, C0=0RD and D0=1LC. Consider the 64 full two-slot refinements that also fix the moves C1 and D1, choosing their independent write and direction bits arbitrarily, but **restricting their next state to either C or D**. Thus each move has two writes × two directions × two next states = 8 choices, and the pair has exactly `8²=64` possibilities. The other six transitions remain arbitrary, including genuine halting transitions.

For every such pair, **all 25⁶ full transition-table completions are blank-start nonhalting.** The original-source Lean theorem is

```lean
BB6.Agent50Raw34Closed.all_sixtyfour
  (c1 d1 : Move)
  (h1 : c1 ∈ closedMoves)
  (h2 : d1 ∈ closedMoves)
  (m : Machine)
  (hm : compatible (parent c1 d1) m) :
  NeverHalts m
```

where `closedMoves` is the literal list of the eight `(write,direction,next state)` outcomes with next state C or D. The source separately checks `closedMoves.length=8`, `closedMoves.Nodup`, and that every listed move has successor C or D.

## Why a tape invariant is unnecessary

The first three blank-start moves are A0, B0, C0 and place the control state at D, with the head at position 3. Lean checks this exact three-step partial-machine prefix via `finitePartialRun_sound`. Thereafter, every read in either state C or D is defined and nonhalting: C0 always moves to D, D0 always moves to C, and C1/D1 have been restricted to move to either C or D. Consequently the finite state set `{C,D}` is closed *under every possible tape symbol*, without any restriction on the tape contents.

The source proves a parametric one-step lemma `closed_step`, then `closed_run` by induction over arbitrarily many transitions and `never` by concatenating the finite entry prefix with the closed future. This is a structural nonhalting certificate: it applies to growing, periodic, chaotic, or otherwise complicated tape evolutions equally. It does not depend on a simulation cutoff or a busy-beaver step bound.

## Count and relationship to prior Raw34 theorems

Each of the 64 disjoint closed `(C1,D1)` pairs represents `25⁶=244,140,625` total physical six-state, two-symbol tables; the entire closed component therefore certifies **`64·25⁶=15,625,000,000`** tables. This should **not** be added wholesale to other Raw34 family counts, because most closed cases were already certified by shorter right/left side-cycle recurrences.

The [85-certificate side-cycle result](2026-11-27-raw34-eightyfive-infinite-rays-agent50.md) covers 11 whole first-level D1 children and 74 second-level children. The independently certified [exact unary-growth child](2026-11-28-raw34-unary-growth-agent50.md) covers D1=1RD, C1=1LC. By exact literal D1/C1 transition comparison, 63 of the 64 closed pairs fall within these earlier accepted cylinders (the eleven whole D1 cases, 74 second-level cases, or unary growth). The **one additional family** not previously covered is

```
1RB---_1RC---_0RD0LC_1LC1RD_------_------
```

with C1=0LC, D1=1RD. It exhibited increasingly long binary-counter-like epochs under finite simulation, but that behavior need not be analyzed at all to prove its nonhalting: the C–D control component remains closed. This new six-hole cylinder contributes another `25⁶=244,140,625` disjoint complete machines. The exact current Raw34 aggregate is therefore

\[
11\cdot25^7+76\cdot25^6
=85\,693\,359\,375
\]

proven nonhalting physical tables, without double counting. This cardinality is a local exact certified-set count; Raw34's other children and its global residual Cover remain unsolved.

## Reproducibility and proof dependencies

The complete standalone source is [Raw34ClosedComponent.lean](../im-results/agent50-raw34-firsthole/Raw34ClosedComponent.lean), importing the source-proved finite-transition semantics and kernel soundness. **Lean 4.36.0-rc2** compiled all nine source modules in [CI run 46086179976](https://github.com/FlareZ123/bb6/actions/runs/46086179976), artifact [15239316293](https://github.com/FlareZ123/bb6/actions/runs/46086179976/artifacts/15239316293), zip SHA256 `daa00ac71fbf695358f06aa60649a202ab9295d268c2fff40ea8630e796559f6`. The `#print axioms` profile of `all_sixtyfour` is exactly `[propext, Classical.choice, Quot.sound]`. The deterministic source runner is `mode=raw34-closed` in [.github/workflows/agent50-raw47-lifted.yml](../.github/workflows/agent50-raw47-lifted.yml).

The broader re-usable method is to recognize a finite, all-symbol, nonhalting closed control-state set after a finite certified entry. It can discharge apparent high-complexity tape-growth cases with a purely graph-theoretic invariant. The result settles neither the full Raw34 parent nor the remaining global BB(6) cases.
