# S4 rooted 18-coordinate projection: exact finite cycle and sparse necessary halting phases

**Scope and conclusion.** This is a reproducible, exact-integer intermediate result for the original S4 candidate `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`. It uses the **source-certified** reduced root at return 5,457 and the source-certified all-depth prefix-causality law. The new long-cycle equalities and phase counts are **native C++ finite calculations**, with selected independent Python cross-checks, **not yet Lean-kernel numerical certificates**. The genuine suffix remains unbounded and S4/BB(6) are unresolved.

## Root-connected theorem (conditional on survival)

Let `p18` be the first 18 entries of the source-certified S4 reduced stack at return 5,457:
```text
[283,906,982,3490,3734,5935,13580,109210,171050,
 366446,435688,443554,1702180,1770018,211301,281569,35137,35134]
```
Let `q(n)=pp^n(p18)` where `pp=gp(219) ∘ gp(290) ∘ gp(509)` is the *total length-preserving prefix map* proved source-compatible in [the parent dossier](README.md). Define `B=327680` and `T=64B=20971520`.

The exact finite computation in [deep_cycle_census.cpp](deep_cycle_census.cpp) establishes
```text
q(4B) = q(68B),  hence q(4B+n) = q(4B+(n mod T)) for every n.
```
The root connection is rigorous under the established source projection theorem: if the actual source reduced run survives through return `5457+n`, then its first 18 digits equal `q(n)`. This theorem **does not** assume or conclude survival through `5457+4B`.

For each stage `j=0,1,2`, put `c_j=(509,290,219)_j`, and define the stage prefix `q_j(n)` by applying the first `j` total `gp` maps to `q(n)`. The necessary stopping residue is
```text
(W(q_j(n)) + c_j) mod 2^18 = 0,
W(xs) = sum_i (xs[i]+1)*2^i.
```
The source `G_none_iff_power` theorem and `W(prefix++suffix)=W(prefix)+2^18 W(suffix)` prove that **any first actual S4 stopping event at `5457+n` with `n>=4B`** must satisfy one of these congruences, with `n-4B` interpreted modulo `T`.

There are exactly **386 stage-candidate phases** in one `T`-period, split as **93, 110, 183** for stages `G509,G290,G219`. They are disjoint by the earlier source-supported nine-digit stage-disjoint census, since a zero residue modulo `2^18` also vanishes modulo `2^9`. Thus there are `20,971,134` phase residues per period at which **no possible suffix** can cause a stop. The exclusion fraction is approximately **99.9981594%** of the period. The 386 candidates remain **necessary only**; the actual suffix has not been decided.

## Intermediate periods, exact computation

The same program proves the following finite block-boundary equalities and period counts. The `preperiod` column counts full `B`-blocks after return 5457, and all periods below are witnessed, rather than claimed to be globally minimal over every time unit.

| Projected digits | Preperiod in B blocks | Period in B blocks | Candidate stage counts over period | Total candidates |
| --- | ---: | ---: | --- | ---: |
| 10 | 0 | 1 | 245 / 392 / 799 | 1436 |
| 13 | 1 | 1 | 32 / 40 / 106 | 178 |
| 16 | 1 | 4 | 23 / 28 / 48 | 99 |
| 17 | 2 | 16 | 48 / 55 / 94 | 197 |
| 18 | 4 | 64 | 93 / 110 / 183 | 386 |

The program also verifies the intervening 11-, 12-, 14- and 15-coordinate period equalities. A 16-coordinate source-survival path after return `5457+B` consequently has only 99 candidate phases modulo `4B`. The eventual period grows with depth, so a smaller fraction of hazardous phases does **not** imply a finite-depth proof of all-time nonhalting.

## Finite proof mechanism and reproducibility

The committed C++20 code is intentionally short and self-contained. It evaluates 68 blocks of 327,680 `pp` operations, asserts each listed cycle equality and the exact stage counts, and checks a conservative 64-bit arithmetic bound on the coordinate values used in the weighted residue test. The `gate` function implements the exact total `hp/gp` prefix map; it intentionally does **not** use the full-stack halting `G` evaluator on a truncated prefix. The 10-/11-/13-digit checkpoints and first blocks were independently reproduced with the Python `ninth_digit_candidate.gp` recurrence, and the 16-/18-digit stage sums were cross-checked in a separate local C++ scan.

In a C++20 build with assertions enabled, compile `deep_cycle_census.cpp` and run the executable. It prints stage counts and exits successfully only after all equalities/count assertions pass. The prior source obligations are already fulfilled by [S4PrefixNinthCycle.lean](S4PrefixNinthCycle.lean) and the genuine-root 5,457 certificate in [S4PrefixNinthBase.lean](S4PrefixNinthBase.lean), original-source [CI 42643801696](https://github.com/FlareZ123/bb6/actions/runs/42643801696). The new 18-dimensional 21-million-step arithmetic identity itself still requires a dedicated Lean/kernel certificate for a fully source-kernel-verified statement.

## Remaining mathematical target

The proved source projection together with finite arithmetic gives an **infinite periodic exclusion of stopping phases**, but permits 386 stopping-gate candidates every `T` returns. A proof that the authentic, history-constrained suffix avoids these candidates at every future period, or a genuine halt witness, is still required. Merely extending this atlas to further fixed depths risks diminishing returns: synthetic suffixes can imitate source-gate powers while retaining coarse rooted statistics (see [same-shape completion](exact-shape-gate.md)). The promising route is to combine these phase constraints with a true full-stack renewal invariant, not to infer nonhalting from projected periodicity.
