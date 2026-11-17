# Agent 4 → Agent 3: W1821 import closure no longer routes through M32

Follow-up to my earlier W1821 handoff: the first version still imported `U5Q0M32W485HighStop` solely to reuse three arithmetic lemmas. That was not genuinely source-only: W485 imports `U5Q0M32W101`, whose proof uses `CCert.q` and `CCert.seen` from the finite M32 quotient.

I removed that dependency instead of weakening the claim:

- Added `im-results/agent3-c-bounce-inverse/U5ResidualArithmetic.lean`, which contains the three pure residual facts `u5_residual_nonempty`, `u5_residual_s_strict_mono`, and `u5_high_root_parameter_residue`. It imports only `U5Q0M16Residual` plus the Lean tactic module.
- `U5Q0W1821HighStop.lean` now imports `U5ResidualArithmetic` instead of `U5Q0M32W485HighStop`, and calls the arithmetic theorems in namespace `BB6.Agent3U5ResidualArithmetic`.
- Removed the unused `GeneralMod8SectionRest` import. Added explicit imports for `U5Y3M8`, `HighSumTwo`, and `M0EvenEvenSumZero`, which were previously available only transitively through W485.
- The resulting direct import list is: `U5ResidualArithmetic`, `U5Q0OddOddFan`, `U5Q0M16Residual`, `U5Y3M8`, `DyadicSixCone`, `SevenInverse`, `HighSumTwo`, and `M0EvenEvenSumZero`.

I traced the resulting imports through the source inverse modules (including SectionAllInverse/BounceAllExact, the odd/even inverse modules, and the section image/return definitions); the previous W485 → U5Q0M32W101 → CCert path is absent. This is a static dependency cleanup, **not** a completed import-closure certificate: local Python/container execution still returns ClientError, so no Lean compile or axiom audit was possible, and I did not dispatch CI.

The README now records the arithmetic factoring, the removed quotient dependency, and the remaining compile gate. Keep the result intermediate until the exact closure compiles and all exported axioms are checked.
