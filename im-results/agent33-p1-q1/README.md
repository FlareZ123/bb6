# Agent 33: exact P1 n=18 inverse-cone audit candidate (2026-11-03)

**Status:** An independently reproduced finite inverse-cone closure and a generated, sorry-free Lean proof candidate are committed. The complete proof compiles locally against signature-compatible *development mocks*, but has **not** been checked against the unchanged original repository imports. The required original-source GitHub Actions run [41596093717](https://github.com/FlareZ123/bb6/actions/runs/41596093717) terminated before usable steps/logs (both jobs failed; logs HTTP 404), consistent with concurrent CI infrastructure failures documented by Agents 8 and 3. Therefore **do not cite this as an established source-certified theorem**, a complete Machine P1 nonhalting proof, or a BB(6) decision.

## Exact candidate statement and authentic dependencies

The proposed theorem [P1Q1.lean](./P1Q1.lean), `BB6.Agent33Q1.blank_no_critical_18`, states:

```lean
¬ BB6.Agent1.Reach 2 (14*2^18-2*18-10)
```

It reuses unchanged original-source `BB6.Agent45TwoRoot.two_sector_critical_iff_feeders 1`, reducing the actual blank-entry P1 critical index 18 to two physical accelerated feeders, and `BB6.Agent4Cone.blocked_no_reach`, with authentic `BB6.Agent47P1.inverseAt` and `inverse_at_depth_le_of_nonzero_mod` for complete source inverse branching. The exact feeder roots for `u2 1 = 458745` are:

- L0: `(1834976,1834989)`
- L1: `(2752468,917495)`

This proof concerns one specific critical index only. Other possible P1 halting indices, the P1 root decision, and BB(6) remain open.

## Reproducible finite arithmetic census

[check_cone.py](./check_cone.py) independently executes original `inverseAt` recurrence as integer arithmetic and exhausts the odd-continuation branches with no numerical depth/queue cap. For `P=2^16=65536`, the output is:

| Feeder | Odd hubs | Mod-4 exits | Odd continuations | Even exits | Largest odd depth | Even-exit `a+12` range |
|---|---:|---:|---:|---:|---:|---|
| L0 | 24 | 41 | 23 | 10 | 7 | 2053600–3368228 |
| L1 | 26 | 36 | 25 | 14 | 7 | 2022012–3594696 |

All 24 even exits satisfy `28*2^16 < a+12 < 56*2^16`, the strict interval between consecutive numbers of the form `14*2^j`. The remaining 77 mod-4 exits have `a%4=2`. The authenticated original reachability lemmas forbid these exits. Every odd internal hub is checked for every `inverseAt` depth via the exact nonzero-modulus depth ceiling, excluding the exceptional input `c=1`.

## Lean proof and trust boundary

The complete 50-hub, ~126 KB `P1Q1.lean` file is expanded and readable, contains no explicit `sorry`, and constructs `Blocked` proofs in a dependency-first order. A **local** Lean 4.36.0-rc2 compile under signature-compatible mock declarations finished with exit code zero, but the mock `Reach`, `GAncestor`, `inverse_at_depth_le_of_nonzero_mod`, `blocked_no_reach`, and `two_sector_critical_iff_feeders` were axiomatized solely for type/proof-shape testing. This does not authenticate the mathematical theorem. On a functioning runner, the existing manual [`agent1-p1-quarter.yml`](../../.github/workflows/agent1-p1-quarter.yml) now compiles `P1Q1.lean` immediately after reconstructing the unchanged relevant original Lean imports and prints `#print axioms blank_no_critical_18`. Only a successful original-source compile with exactly the standard Lean axioms (and a review of the source revision) promotes this candidate to verified status. Keep under `im-results/` until independent validity and relevance review.

CI attempt [41596093717](https://github.com/FlareZ123/bb6/actions/runs/41596093717) at original-source head `98c60a2d285291d2fa6125b65d84dcf3bfe398d7` had both `source-certify` and `agent23-root-wall` jobs terminate before their logs became available; **no theorem compilation result can be inferred from the red status**. No repeated unchanged CI run should be dispatched until the runner is confirmed functional.

## Relation to the broader R002 programme

This exact finite `q=1` cone lies inside the still unresolved `n=16q+2` P1 critical family and is compatible with Agent50's all-q theorem that every surviving affine-wall cone history needs at least two positive-depth inversions. Its finite size is an atomic candidate elimination, not a parameter-uniform method. The major remaining mathematical objectives are an all-q wall exclusion or a decisive blank-orbit invariant, plus the exponential-cost and exceptional-exit alternatives. Reconcile with the R002 source-ledger before claiming external novelty.
