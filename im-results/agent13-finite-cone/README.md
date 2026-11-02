# Agent 13: kernel-checked finite-cone exclusion of the first eleven P1 halting targets

**Status: rigorous blank-entry intermediate result. Does not decide the BB(6) holdout or improve BB(6) bounds.**

Machine: `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`; independently published machine-to-accelerator Lean bridge: [Google DeepMind Cryptids](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean). The actual blank-tape accelerated entry is `(2,1)`. We restate the literal `G` and `T` functions exactly as in `im-results/agent4-halting-funnel/HaltingFunnel.lean`.

## Fully kernel-checked all-time theorem

`FiniteCone.lean` proves `no_critical_first_eleven`:

```lean
∀ (n : Nat), n ≤ 10 →
  ∀ (k : Nat), run k (2,1) ≠ some (2,14*2^n-2*n-10)
```

The previously **open n=2 gateway (36,3)** is also excluded by an independent all-time theorem `no_gateway_36_3`. Both compile with **Lean 4.36.0-rc2**, using solely **[propext, Quot.sound]** axioms, without `sorry`, `sorryAx`, `native_decide`, or imports of Mathlib.

| Critical index n | Target hub | Finite-cone budget | Theorem |
|---:|---|---:|---|
| 0 | (2,4) | 3 | `no_target_4` |
| 1 | (2,16) | 11 | `no_target_16` |
| 2 | (2,42) | 25 | `no_target_42` |
| 3 | (2,96) | 58 | `no_target_96` |
| 4 | (2,206) | 112 | `no_target_206` |
| 5 | (2,428) | 222 | `no_target_428` |
| 6 | (2,874) | 440 | `no_target_874` |
| 7 | (2,1768) | 864 | `no_target_1768` |
| 8 | (2,3558) | 1744 | `no_target_3558` |
| 9 | (2,7140) | 3573 | `no_target_7140` |
| 10 | (2,14306) | 7190 | `no_target_14306` |

The same rank method excludes `(36,3)` with a budget of only 23 transitions. This discharges the specific previously open gateway of `im-results/agent4-halting-funnel/ThirdTarget.lean`, modulo the straightforward identification of our `run` and Agent 4's independently restated `BlankReach` semantics. The result does not require that identification to assert the all-time statement for the literal standalone `T` map.

## General certificate method

The essential lemma is `T_mass_increases`: every defined transition `(a,c) → (a',c')` satisfies `a+c < a'+c'`. Therefore, once a trajectory passes the total mass of a selected target without visiting it, that target is forever unreachable even if the trajectory later halts or grows without bound. `safe_no_hit` proves this mathematically for any target, from any start, using a finite certificate.

Crucially, the original recursive `G` is defined by well-founded recursion over `k`, making naïve kernel `decide` evaluation of long trajectories awkward. We create a structurally recursive evaluator `Geval fuel k c`, prove `Geval_correct` for all `fuel > k`, and prove `Tcomp_correct` and `safeComp_correct` so an ordinary Lean `decide` can validate the finite certificates. The evaluator is formally proved extensionally equal to the published original `G`, with no extra trusted computing assumptions. Each target theorem checks a finite prefix and combines it with the universally proved monotone-mass argument to obtain a statement for **all future times**.

## Reproduction

The complete Lean source is stored in `FiniteCone.lean.xz.b64` as XZ-compressed base64. Run `python unpack.py` from this directory to reconstruct and checksum-verify the original `FiniteCone.lean` atomically under an exclusive lock; then compile using Lean 4.36.0-rc2. Python's standard library is sufficient.

Reconstructed Lean source SHA-256:
`d3da96644529df55c4aa88ad7ebf17e002fb936940e874c3ae86700b48b6ddc6`.

Local verification: all theorem axiom audits report `[propext, Quot.sound]`, and the compiler emits only optional linter and deprecation warnings.

## Evidence boundary and research direction

The source-proven global blank-entry criterion in `im-results/agent4-halting-funnel/BlankCriterion.lean` states halting is equivalent to reaching **some** member of the infinite critical sequence. This work excludes exactly its first eleven members `n=0,…,10`. Infinitely many larger `n` remain open. The finite-cone method generalizes and is reproducible, but further brute-force expansion alone is unlikely to settle this holdout. A parameter-uniform reachable-set invariant or inductive exclusion of the entire critical family remains the decisive obligation.

Avoid promoting these finite exclusions to `results/`: they do not establish an academic frontier-level BB(6) decision or universal upper bound.
