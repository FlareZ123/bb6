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

## Proof dependencies and exact scope

The [`MidAposBoundary.lean`](../agent32-429-high2-prefix/MidAposBoundary.lean) source return sends all even inputs `midApos 0 (2k) 5` in exactly `26k+177` primitive steps to a zipper `junc 3 0 (4k+17)`, and all odd `midApos 0 (2k+1) 5` in `26k+354` steps to `junc 11 0 (4k+10)`. Its theorem statements had previously failed elaboration due to a redundant `congr 1` before a `rw` in an auxiliary list-identity. Removing that redundant tactic, after an exact isolated Lean preflight, allowed the **entire** source module to compile with no `sorryAx`; checked [CI 42522314710](https://github.com/FlareZ123/bb6/actions/runs/42522314710).

To convert those zipper returns into actual raw halting statements, `W5FatalMidA.lean` invokes the original raw displacement bridge `source_runWithDelta_rep`, Agent18's full-tape `represented_junc_eq_translatedJ`, Agent32's exact raw high-three `j_high3_ladder`, and Agent1's exact `j_fatal_branch`. Each theorem's source checked `#print axioms` contains only Lean's normal logical axioms (no `sorryAx`). The same manual-only [raw source audit workflow](../../.github/workflows/agent30-429-first-gate-raw.yml) recompiles the whole dependency chain. Source is pinned by the immutable CI commit SHA; no source external or guessed proof assumptions.

**Important limitation:** The quantified `c` is an *arbitrarily prepared physical tape satisfying the entire zipper representation*. It is not claimed to be reachable from the authentic all-zero starting tape. A genuine blank-root witness for one of these families, or a proof that none can occur together with control over the remaining cases, would be needed to decide #429. The elementary generic first-branch ancestry overlaps preexisting synthetic-ray methods (e.g. [Agent6's inverse ray](../agent6-harmonic429/BB429InverseRay.lean)); the distinct contribution here is the repaired, source-certified **right-five MidA-to-Junc return and its composed all-parameter physical halting families**, within this repository.

No work here is claimed to be an externally novel academic result; all artifacts belong to `im-results/`.
