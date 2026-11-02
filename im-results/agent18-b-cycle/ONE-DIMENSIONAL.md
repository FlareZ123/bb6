# Agent 18: a two-branch scalar model for an undecided BB(6) holdout

**Scope:** intermediate, source-bridged mathematical reduction. This document does not claim the holdout halts, never halts, or changes any BB(6) bound. The equation is a more economical representation of Agent 5's already known three-counter-to-two-counter collapse.

Target: `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`. Its original blank-tape machine semantics were proved equivalent to the exact published three-counter acceleration by the Google DeepMind Cryptids module at pinned revision `ced8f9f44f67a167d5ecc03e687b048c67926371`. Agent 18's import-based proof of the connection is `Agent18BBridge.lean`, passing [manual CI run 41387857461](https://github.com/FlareZ123/bb6/actions/runs/41387857461).

## Exact two-branch scalar conjugacy

Agent 5 reduced a complete positive-a countdown to the parity-memory transducer

```
F(p,d) = (d % 2, 3*(d/2)+2+4*p),    p in {0,1}.
```

Define a *different* scalar encoding from the earlier base-four formulation:

```
z = 2*d+3*p,       z >= 0, z != 1.
```

The local theorem `F_enc` proves for every natural d and p≤1 that the entire transducer is conjugate to

```
g(z) = 3*floor(z/2)+4+5*(z mod 2)
     = { 3*u+4,  z=2*u;
       { 3*u+9,  z=2*u+1.
```

Unlike the previous scalar encoding (four base-four branches), this encoding uses **two base-two branches** and no extra parity-memory state. `conj_iter` proves the conjugacy for *every* iteration count and all admissible initial states. `enc_parity` establishes `p=z mod2`.

## Fully scalar blank-entry halting criterion

Starting with `A_0=3`, define *entirely on natural numbers*

```
Z_n   = g^[A_n](0)
A_(n+1) = Z_n + 9 - 3*(Z_n mod 2).
```

The recursion is purely syntactic and continues even after a hypothetical earlier halting phase. `scalarA_eq_resetA` proves this recursively defined sequence agrees *universally* with the exact three-counter return indices. `raw_criterion_local` proves the following complete iff for the three-counter acceleration:

```
Halts(3,0,0)  ↔  ∃ n : Nat, Z_n mod 2 = 0.
```

`Agent18OneDimBridge.lean` composes this with the kernel-checked original-machine semantic bridge to produce:

```lean
raw_halts_iff_two_branch :
  IsHalt Source.target ↔ ∃ n : Nat, (OneDim.iterG (OneDim.scalarA n) 0)%2=0
```

**Remaining decisive question:** is one of these recursively sampled scalar iterates even? The first sampled values (3 iterations, then 25, then 227097) are odd. The third sample has tens of thousands of decimal digits; no finite test resolves the infinite question.

## Verification

`BOneDim.lean` compiled under supplied Lean 4.36.0-rc2 with no `sorryAx` and `#print axioms` for `F_enc`, `conj_iter`, `scalarA_eq_resetA`, and `raw_criterion_local` reported only `propext`, `Classical.choice`, `Quot.sound`. The pinned-source manual CI workflow `.github/workflows/agent18-b-bridge.yml` also compiles `Agent18OneDimBridge.lean`, with its independently checkable exact run recorded at GitHub Actions. This checked proof is the basis for treating the formula as an original-machine equivalence; do not count the standalone local model alone as a raw-machine theorem.

This compact scalar normalization could support further algebraic or 2-adic analysis of the sparsely sampled parity sequence. It does not imply the answer and should remain in `im-results/` until a globally decisive theorem is found.
