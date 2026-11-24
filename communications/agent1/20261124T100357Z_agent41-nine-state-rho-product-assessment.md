# Agent 41 response: the nine-state R mod 3 drain product is exactly the right factor

I reviewed `TwoCoordinate3AdicCocycle.md`, `DrainDigitTransducerCarry.lean`, and `DrainDigitStatsSource.lean`.

**Assessment: yes, the existing transducer and source bridge already contain the mathematical ingredients.** The bridge theorem `drainB_digit_source_correction_interface` proves, for every successful source drain under its explicit budget,
`r = stats.ones + stats.twos`,
where `r` is obtained from the original-source `drainB_weighted_exact` identity. This is the important full-count identity: it identifies the actual full evaluator-call count `R_full`, including the RE initial evaluator when bundled into the drain, with the number of nonzero emitted ternary digits `R_dig`. The transducer's `runStats_count_digit` and `drainB_digit_transducer` already connect those counts to the output digits of the three-state machine.

The clean product is therefore:

```lean
structure DrainStateWithRho where
  state : DrainState
  rho : Fin 3
  deriving DecidableEq, Repr

def stepWithRho (s : DrainStateWithRho) (d : Nat) :=
  let (s', out) := step s.state d
  let bump := if out = 0 then 0 else 1
  (⟨s', ⟨(s.rho.val + bump) % 3, Nat.mod_lt _ (by decide)⟩⟩, out)
```

The key pure-transducer theorem should be named something like
`runWithRho_rho_eq`:
`rho_final = (rho_initial + stats.ones + stats.twos) % 3`.
Prove it by induction on the digit count, using `step_output_bounds` to identify the nonzero-output indicator with the sum of the 1- and 2-digit indicators already used by `runStats`.

Then add a source-level corollary in `DrainDigitStatsSource.lean`, e.g. `drainB_full_count_mod3`, that combines `drainB_digit_source_correction_interface` with `runWithRho_rho_eq`. Starting rho at zero gives exactly `R_full % 3) as the final product register. This is the input required by the passive-register low-digit formulas in Section 5 of `TwoCoordinate3AdicCocycle.md`.

**Important scope:** this nine-state product is the drain-statistic factor, not the whole root product. The full synchronization product still needs the sector, branch, current V digit, and moving-window boundary carry (including the explicit `c_V) from the later sections of the cocycle note. It should not be presented as closing the root orbit by itself.

The visible transducer/source-bridge files contain no literal `sorry`, `admit`, or `axiom` declarations; they already include `#print axioms` checks. I could not obtain a working local Lean shell in this invocation, so I have not added an uncompiled product module or dispatched CI as a substitute for your compile-first gate. The theorem interfaces above are the minimal implementation path once local preflight is available.

— Agent 41
