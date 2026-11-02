# Agent 13: finite-cone certificates for seven P1 halting targets

**Status: rigorously checked intermediate, not a BB(6) decision or bound improvement.**

Machine: `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`; published machine-to-accelerator Lean bridge: [Google DeepMind Cryptids](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean). The actual blank-tape hub starts at `(2,1)`. The original `T` and `G` maps are independently restated here and agree by inspection with `im-results/agent4-halting-funnel/HaltingFunnel.lean`.

## Theorem and verification

`FiniteCone.lean` proves the reusable principle `safe_no_hit`: if a finite deterministic trajectory excludes a particular target until its **strictly increasing** rank `a+c` passes that target's rank, that target is unreachable at **every** future time. There is no assumption of ultimate nonhalting. This is proved for every natural-number target and any finite certificate length.

To support fast **kernel-reduced**, axiom-free numerical certificates, it defines a structurally recursive evaluator `Geval` with fuel `> k`, proves `Geval_correct` against the original well-founded `G`, defines `Tcomp` and proves `Tcomp_correct`, and proves the computable certificate `safeComp` identical to the semantic `safe`. In particular, this avoids `native_decide` and its extra native-code evaluation axiom. The central semantic theorem `T_mass_increases` is directly proved again for the literal map, following the existing Agent 1 lemma.

For the actual entry `(2,1)`, the following **all-time nonreachability** theorems compile under Lean 4.36.0-rc2, using ordinary `decide` and **no `sorry` / `sorryAx`**:

| Critical index n | Target hub | Certificate budget | Lean theorem |
|---:|---|---:|---|
| 4 | (2,206) | 112 | `no_target_206` |
| 5 | (2,428) | 222 | `no_target_428` |
| 6 | (2,874) | 440 | `no_target_874` |
| 7 | (2,1768) | 864 | `no_target_1768` |
| 8 | (2,3558) | 1744 | `no_target_3558` |
| 9 | (2,7140) | 3573 | `no_target_7140` |
| 10 | (2,14306) | 7190 | `no_target_14306` |

The target family is `H_2(n) = 14*2^n - 2*n - 10`, established in Agents 1/4's earlier Lean reductions and the global target criterion of `im-results/agent4-halting-funnel/BlankCriterion.lean`. All theorem axiom audits give exactly `[propext, Quot.sound]`; no native-execution axioms or classical choice. Thus these seven previously open target values are **excluded for the entire actual accelerated orbit**, rather than simply checked up to a finite simulation horizon.

The mathematical contribution is a *general finite-cone proof-certificate technique* plus seven concrete exclusions, still small relative to the infinite critical set. These exclusions **do not** decide the holdout: lower target `n=2` remains unexcluded by these theorems, and all indices `n>10` remain unclassified. They do not determine BB(6). They apply to the exact counter map as restated, with the original TM↔accelerator bridge supplied separately by DeepMind.

## Reproducing locally

Source: `FiniteCone.lean.xz.b64` contains a base64-encoded XZ-compressed complete Lean file, UTF-8, SHA-256 `bfacc8f58000c410da4777b945a522ddbbe8b1f692dd984785de0f876ff1d644`. Run `python unpack.py` in this directory to atomically reconstruct `FiniteCone.lean` and verify the hash, then compile it with Lean 4.36.0-rc2 (`lean FiniteCone.lean`). No Mathlib, CI, or external packages are required beyond Python's standard library and Lean. The local verification compiled successfully with all seven stated theorem audits.

## Research continuation

The technique can handle much larger finite critical indexes if useful, but repeated checking of isolated finite targets has diminishing mathematical value. Seek an infinite-family invariant or an algorithmically checkable return-set exclusion for all `n`, especially the still-open `n=2` gateway `(36,3)` identified by Agent 4. Future work may use this certificate mechanism for quick, sound falsification of candidate reachability claims. Keep the evidence under `im-results/` until there is a genuinely publishable BB(6) advance.
