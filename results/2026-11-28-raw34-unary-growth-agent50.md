# Raw34 unary-growth cylinder: an unconditional nonhalting proof for 244,140,625 six-state machines

**Status: original-source Lean 4.36.0-rc2 accepted, standard axioms only.** This is a *complete universal nonhalting theorem* for one six-hole cylinder, not a global Busy Beaver maximum and not a complete Raw34 parent bound.

## Machine and exact growth law

Consider the six-transition partial two-symbol six-state table

```
1RB---_1RC---_0RD1LC_1LC1RD_------_------
```

The six fixed transitions are A0=1RB, B0=1RC, C0=0RD, C1=1LC, D0=1LC, D1=1RD. The other six entries remain completely arbitrary; some may contain immediate halts. Every total machine extending these six instructions **never halts from the blank tape**.

In the ordinary source-level zipper transition semantics `BB6Coverage.Agent31Pump.run0`, let `rep [true] n` denote `n` consecutive marked cells, and define the family

```lean
family n := ⟨3, [false] ++ rep [true] n ++ [false,true,true], []⟩
```

The control state is D, the head scans a fresh zero at tape position `n+3`, and the tape has ones at positions 0, 1, and 3 through `n+2`. Thus the frontier advances by exactly one cell per epoch. The kernel-checked source gives:

```lean
first  : run0 p 3 ⟨0,[],[]⟩ = some (family 0)
growth : ∀ n, run0 p (2*n+3) (family n) = some (family (n+1))
never  : ∀ m : Machine, compatible p m → NeverHalts m
```

The growth step has five phases: D0 writes a one and moves left; C1 sweeps left across `n` ones; C0 turns right; D1 sweeps right across `n` ones; then one more D1 transition enters the next fresh zero. The one-cell identities are `left_one` and `right_one`, and the arbitrary-length inductions come from the reusable, previously source-proved `sweepL` and `sweepR` lemmas. Joining the five phases gives the exact epoch cost `1+n+1+n+1=2n+3`. Every epoch cost is positive, so `never_of_growth` supplies arbitrarily long live prefixes for *any compatible total machine*, not merely for the particular six-transition sparse simulation.

The absolute time of the `k`-th family configuration is `3 + ∑_{j<k}(2j+3) = 3+k^2+2k`. This is a quadratic-time recurrent growth structure, not a finite repeating cycle.

## Quantitative coverage and disjointness

There are exactly six unspecified tape-symbol/state entries, each with 24 ordinary transitions or one genuine halting transition. Therefore the universal nonhalting theorem covers **`25^6=244,140,625`** distinct physical total six-state machine tables.

This is disjoint from the 85 previously source-certified [Raw34 side-cycle cylinders](2026-11-27-raw34-eightyfive-infinite-rays-agent50.md): the first level covers eleven D1 values not including `1RD`, and the earlier `1RD` second-level certificates have different C1 values from this `1LC` growth child. Together they prove blank-tape nonhalting for

\[
11\cdot25^7+75\cdot25^6=85\,449\,218\,750
\]

physical completions of the eight-hole Raw34 parent. This is a local certified count; the remaining Raw34 children and Canonical40 root inclusion are not yet consumed by a complete Cover.

## Original-source proof acceptance

The complete standalone original Lean source is [Raw34UnaryGrowth.lean](../im-results/agent50-raw34-firsthole/Raw34UnaryGrowth.lean). Its five theorem/check statements were compiled in the full six-module source closure by **Lean 4.36.0-rc2** in [CI run 46085752374](https://github.com/FlareZ123/bb6/actions/runs/46085752374), artifact [15238539861](https://github.com/FlareZ123/bb6/actions/runs/46085752374/artifacts/15238539861), zip SHA-256 `fc862bb51fd07e274d59c5121a4e6d766f04c9fc93d31cf2a1ec20c6c51e7a34`. The `#print axioms` output for `never` is exactly `[propext, Quot.sound]`; the intermediate first and sweep-step theorems also use only standard axioms. No `sorryAx` or `native_decide` is used. The manual proof runner is `mode=raw34-growth` in [.github/workflows/agent50-raw47-lifted.yml](../.github/workflows/agent50-raw47-lifted.yml).

## Remaining mechanism to close

The other Raw34 depth-two growth candidate is

```
1RB---_1RC---_0RD0LC_1LC1RD_------_------
```

with C1=0LC rather than 1LC. Its observable frontier increments appear exponentially spaced rather than linearly, consistent with a binary-counter carry mechanism. That statement is *only a finite simulation observation* at this stage; a separate symbolic invariant is needed to show all-time nonhalting. The surrounding Raw34 parent also has many genuinely unresolved finite-depth children. No global BB(6) value or upper bound follows from the one-cylinder theorem.
