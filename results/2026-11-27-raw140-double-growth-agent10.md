# Two Raw140 nonhalting cylinders via an arbitrary-word bounce

**Accepted Lean theorem, 2026-11-27.** The two literal partial tables are

```
1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0LB---
1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---
```

They correspond to local first-hole discovery indices 73 and 80, not global Canonical58 indices. Every completion of F1 is nonhalting.

## Mathematical result

Use little-endian three-cell symbols and nearest-first stacks. For the six suffixes
`62,64,6221,6421,6405,62542`, let rho rotate through the displayed order and
C_j(s)=floor((j+rank(s))/6), with rank starting at zero. Write
T(m,n,s)=BR(5^m,(644)^n s), m even >=18, n>=2. The two positive-time returns are

* F0=0LB: T(m,n,s) -> T(2m+14,n-2+C_(m+3)(s),rho^(m+3)(s)).
* F0=0RD: T(m,n,s) -> T(2m+16,n-2+C_(m+5)(s),rho^(m+5)(s)).

Exact entries from blank occur at 42133 steps into T(78,5,62) and 44429 steps into
T(80,5,6221). Each return stays in the invariant and avoids F1. The central new
lemma is the arbitrary-word-preserving sweep
CR(4X,W s) -> DL(5X,W (644)^carry(s) rho(s)), for every word W over {4,6},
with exact duration 22|W|+tailcost(s). It is proved by induction using finite
forward/reverse local paths. Iterating the sweep and two homogeneous conversions
yields the displayed returns.

Full mathematical derivation: [Raw140DoubleGrowthProof.md](../im-results/agent10-nov26-cryptids/Raw140DoubleGrowthProof.md).
Source modules: [local rules](../im-results/agent10-nov26-cryptids/Raw140DoubleLocal.lean),
[parametric core](../im-results/agent10-nov26-cryptids/Raw140DoubleCore.lean),
[closure](../im-results/agent10-nov26-cryptids/Raw140DoubleClosure.lean),
[entry](../im-results/agent10-nov26-cryptids/Raw140DoubleEntry.lean),
[coverage](../im-results/agent10-nov26-cryptids/Raw140DoubleCover.lean).
The final closure uses a positive-time invariant and does not infer nonhalting
from simulation length.

## Acceptance and exact interface

[CI run 45937374742](https://github.com/FlareZ123/bb6/actions/runs/45937374742)
succeeded at source revision `0a985d4ed1727887a17f92b3e6c0f5fd394c46d4`.
Workflow target `double`, Lean 4.36.0-rc2, original repository dependency closure;
both exact table equality bridges and standard-axiom audits succeeded.
The two exported theorems are
`Raw140Double.X4.cover (B : Nat) : Cover (WeightedBound B) Raw140Double.X4.p`
and `Raw140Double.X13.cover (B : Nat) : Cover (WeightedBound B) Raw140Double.X13.p`.
The corresponding `never` theorems quantify all compatible completions. This
settles 50 physical completions under the 25-option coverage convention.
It does not close the three-hole parent or the global Raw140 parent.
No global Canonical58 roster reduction is claimed.
