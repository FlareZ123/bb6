# #429: source-certified right-five MidA halting families, on prepared tapes

**Status (8 November 2026):** Intermediate all-parameter theorem for the **original six-state, two-symbol raw transition table** of machine #429, Lean 4.36.0-rc2. It does **not** decide machine #429 from its initially blank tape, or determine BB(6). The two complete prepared-tape family theorems were checked against the unchanged repository source in [successful manual CI 42522688788](https://github.com/FlareZ123/bb6/actions/runs/42522688788); the prior blocked right-five symbolic source chain is now soundly compiled in [42522314710](https://github.com/FlareZ123/bb6/actions/runs/42522314710).

## Genuine-table theorems

Let `target429` denote the literal complete #429 transition table, `run target429 n c = none` the machine's undefined halting query at or before primitive step count `n`, `Represents` the entire bi-infinite tape relation to a source zipper, and `jConfig u w` the exact prepared J tape. Define
```
K_even(m) = 6 * 2^(4*(m+1)) - 12 - 3*m
K_odd(m)  = 14 * 2^(4*m+1)   - 12 - 3*m.
```
For every `m : Nat`, the new [`W5FatalMidA.lean`](W5FatalMidA.lean) proves that **every** physical configuration `c` representing `midApos 0 (2*K_even(m)) 5` satisfies
```lean
run target429
  ((26*K_even(m)+177)
    + (branchCostSum 3 (4*(m+1))
       + branchCost (branchU 3 (4*(m+1))))) c = none
```
and every physical `c` representing `midApos 0 (2*K_odd(m)+1) 5` satisfies the analogous expression
```lean
run target429
  ((26*K_odd(m)+354)
    + (branchCostSum 11 (4*m+1)
       + branchCost (branchU 11 (4*m+1)))) c = none.
```
The first seed parameters are `K_even(0)=84` and `K_odd(0)=16`. [`FirstGateRays.lean`](FirstGateRays.lean) derives the two closed forms and formally establishes that each index family is strictly increasing, so there really are infinitely many *different prepared initial tapes*. Each theorem is universal over all `m`, with no finite simulation cutoff.

A stronger intermediate theorem in [`FirstGateRaw.lean`](FirstGateRaw.lean) proves for all `u>=1,n` that `jConfig u (anc u n)` halts after the exact sum `branchCostSum u n + branchCost (branchU u n)`, where
```
anc u 0 = 2u-1
anc u (n+1) = (2u+3)+anc (2u+3) n.
```
The arithmetic identity `anc u n + 3n + 2u+13 = 4(u+3)2^n` determines the explicit right-five families from those fixed J endpoints. The source-checked accelerator-only theorem `BB429FirstGateRays.{even_gate_halts,odd_gate_halts}` separately passed [CI 42521779007](https://github.com/FlareZ123/bb6/actions/runs/42521779007), and the independently raw J family passed [CI 42522068921](https://github.com/FlareZ123/bb6/actions/runs/42522068921).

## Exact two-burst low-even source classification

The direct one-burst fatal parameters in the two original right-five endpoints are **completely classified**, not merely exhibited. [`W5FirstBurstComplete.lean`](W5FirstBurstComplete.lean) uses the source-certified `BB429Burst.burst_gateway_iff` to prove for every `k`:
- A first-branch-only prefix from `(3,4k+17)` reaches the fatal gateway **iff** `k=K_even(m)` for some `m`.
- A first-branch-only prefix from `(11,4k+10)` reaches the gateway **iff** `k=K_odd(m)` for some `m`.
Both were checked in [CI 42523491393](https://github.com/FlareZ123/bb6/actions/runs/42523491393).

A second, genuinely different infinite family includes an **exceptional low-even** arithmetic branch:
```
K_two(t) = 14*2^(4t+5) - 23 - 6t
Q(t) = 2^(4t+5).
```
For all `t:Nat`, [`W5TwoBurst.lean`](W5TwoBurst.lean) proves, using the literal 12-branch source map and no `sorryAx`, the exact accelerator statement
```lean
BB429.run (8*t+14) (3,4*K_two(t)+17) = none
```
with the proven intermediate path
```
first^(4t+7): (3,4*K_two+17) → (24Q-3,8Q-42-12t)
low-even:     (24Q-3,8Q-42-12t) → (11,56Q-50-12t)
first^(4t+5): (11,anc 11 (4t+5)) → fatal first-branch gateway
```
This infinite source-only result passed [CI 42524241956](https://github.com/FlareZ123/bb6/actions/runs/42524241956).

[`W5TwoBurstUnique.lean`](W5TwoBurstUnique.lean) establishes a stronger **necessity/uniqueness theorem**: any path from `(3,4k+17)` with `n` high3/first branches, one exact low-even branch, `p` high3/first branches and final fatal boundary must have *exactly* `n=4t+7`, `p=4t+5`, `k=K_two(t)` for some `t`. The proof uses complete source first-prefix formulas, an exponential-width squeeze forcing `n=p+2`, and parity congruences forcing `p≡1 (mod 4)`. Its genuine source audit passed [CI 42524924650](https://github.com/FlareZ123/bb6/actions/runs/42524924650). The strict seed-growth lemma also passed the unmodified-source [CI 42526013341](https://github.com/FlareZ123/bb6/actions/runs/42526013341).

## Precisely isolated physical low-J obligation

The arithmetic low-even state above corresponds to the physical J chart at `J(24Q-3,8Q-42-12t)`, with deficit `2u-w=4*(10Q+9+3t)`. Agent18's [low-J table](../agent18-429-low-j/README.md) experimentally predicts an entire-tape raw physical return to `J(11,56Q-50-12t)`, with physical head displacement `9-2u`, for every `t`. **The all-parameter low-J physical return itself is unproved.**

[`W5TwoBurstRawBridge.lean`](W5TwoBurstRawBridge.lean) isolates exactly this original-machine premise in a Lean theorem `raw_two_burst_of_low_ray`: any certified low-J ray run of `N` primitive steps from `J(u,w)` to the correctly translated `J(11,anc 11 (4t+5))` composes automatically with already certified high3 and fatal raw paths to show the original machine halts from `J(3,4K_two(t)+17)` after the sum of exact primitive costs. This **conditional** original-source theorem passed [CI 42525299970](https://github.com/FlareZ123/bb6/actions/runs/42525299970), without `sorryAx`. It directly identifies a high-value single physical proof goal for Agent18; [targeted communication](../../communications/agent18/20261108T2126Z_agent30-low-even-two-burst-unique-physical-bridge.md).

The first physical case is now **fully source-certified** in [`W5TwoBurstT0.lean`](W5TwoBurstT0.lean): `J(765,214)` moves in exactly **54,333 raw six-state steps** to an entirely equivalent translated `J(11,1742)`, head displacement `-1521`. A `native_decide` certificate of the actual source zipper trace is lifted through `source_runWithDelta_rep` and Agent18's all-tape J equivalence to original infinite-tape physical semantics. Composition with the source-certified raw high3 and fatal transitions proves that the actual six-state machine **halts from the synthetic prepared tape `J(3,1717)` at or before primitive query 1,888,290**. The full original-source audit [CI 42526145633](https://github.com/FlareZ123/bb6/actions/runs/42526145633) passed without `sorryAx`. The simplified literal-query-count theorem `raw_two_burst_t0_exact` is also fully checked in [CI 42526303107](https://github.com/FlareZ123/bb6/actions/runs/42526303107), with the exact source statement `run target429 1888290 (jConfig 3 1717) = none`. This finite example does **not** assert the full two-burst family halts physically or that the authentic blank tape reaches it.

## Proof dependencies and exact scope

The [`MidAposBoundary.lean`](../agent32-429-high2-prefix/MidAposBoundary.lean) source return sends all even inputs `midApos 0 (2k) 5` in exactly `26k+177` primitive steps to a zipper `junc 3 0 (4k+17)`, and all odd `midApos 0 (2k+1) 5` in `26k+354` steps to `junc 11 0 (4k+10)`. Its theorem statements had previously failed elaboration due to a redundant `congr 1` before a `rw` in an auxiliary list-identity. Removing that redundant tactic, after an exact isolated Lean preflight, allowed the **entire** source module to compile with no `sorryAx`; checked [CI 42522314710](https://github.com/FlareZ123/bb6/actions/runs/42522314710).

To convert those zipper returns into actual raw halting statements, `W5FatalMidA.lean` invokes the original raw displacement bridge `source_runWithDelta_rep`, Agent18's full-tape `represented_junc_eq_translatedJ`, Agent32's exact raw high-three `j_high3_ladder`, and Agent1's exact `j_fatal_branch`. Each theorem's source checked `#print axioms` contains only Lean's normal logical axioms (no `sorryAx`). The same manual-only [raw source audit workflow](../../.github/workflows/agent30-429-first-gate-raw.yml) recompiles the whole dependency chain. Source is pinned by the immutable CI commit SHA; no source external or guessed proof assumptions.

**Important limitation:** The quantified `c` is an *arbitrarily prepared physical tape satisfying the entire zipper representation*. It is not claimed to be reachable from the authentic all-zero starting tape. A genuine blank-root witness for one of these families, or a proof that none can occur together with control over the remaining cases, would be needed to decide #429. The elementary generic first-branch ancestry overlaps preexisting synthetic-ray methods (e.g. [Agent6's inverse ray](../agent6-harmonic429/BB429InverseRay.lean)); the distinct contribution here is the repaired, source-certified **right-five MidA-to-Junc return and its composed all-parameter physical halting families**, within this repository.

No work here is claimed to be an externally novel academic result; all artifacts belong to `im-results/`.
