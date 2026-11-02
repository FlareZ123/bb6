# Agent 11: infinite modular exclusions for machine C

These are **Lean-kernel-checked intermediate results**, not a BB(6) solution. The machine is `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, using DeepMind's published accelerator with actual blank-entry state `(5,0,1)`.

## Global reachable-state invariant

For every reachable `(a,k,c)` with `c>=4` and `(a+k)%4>=2`, **`k%2=c%2`**. Proof: the invariant is true at the initial state and preserved by every branch of the accelerator. The high-sector sweep preserves `a+k` and flips the parity of both `k` and `c`. Lean `CParity.reached_parity_good` establishes this for all finite times.

Consequences:

* `side_odd_unreachable`: for **every odd m**, `¬Reach(0,2*m,12*m+23)`.
* `reset_mod4_one_unreachable`: for **every j>=1 with j%4=1**, `¬Reach(2*j+1,3*j+4,0)`. The backward predecessor chain of any reached reset state is exactly `(2j+2,3j,4) → (2j+1,3j+1,3) → (2j+1,3j+3,1) → (2j+1,3j+4,0)`; its first point violates the invariant at `j%4=1`.

## Strongest equivalence

The all-natural Lean theorem `BB6CLine.stops_iff_stronger_gates` proves:

```text
eventual stop from (5,0,1)
iff
  (exists j>=1, j%4 != 1 and Reach(2*j+1,3*j+4,0))
  or
  (exists n>=1, Reach(0,4*n,24*n+23)).
```

The `n=0` side point is also excluded by the separately proved invariant `k=0 implies a is odd`.

The remaining infinite classes are **open**. No halting classification or BB(6) bound improvement is claimed.

## Exact proof preservation

`parity-lean.tar.xz.b64` stores the two complete Lean source files, SHA-256 checked by `reconstruct-parity.py` (requires Python `filelock`; locked atomic writes):

* `CParity.lean` (2497 bytes, SHA-256 `9d1e30042a028e55c919eb91ed4f0d343707aad3c0c928bd719f4a091d0b811a`)
* `CParityGates.lean` (6962 bytes, SHA-256 `e478d7623fd6db1adb40c65f9c62c6fca6897660f1906188ca333d4d841b4aa9`).

Reconstruct the earlier `LowGate.lean`, `BackGate.lean`, and `ResetGate.lean` with `python reconstruct.py`; compile modules in this order: `CLine`, `LowGate`, `BackGate`, `ResetGate`, `CParity`, `CParityGates`. Lean 4.36.0-rc2 reports only standard axioms `[propext, Classical.choice, Quot.sound]`, with **no sorryAx**. The upstream Turing-machine-to-counter bridge is supplied by [DeepMind's original Lean formalization](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean), and our standalone proof copies the counter rules by source inspection.
