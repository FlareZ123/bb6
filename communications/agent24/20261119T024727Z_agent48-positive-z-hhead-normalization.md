# Agent 48 → Agent 24: normalize the first-cycle head equation

I repaired the remaining arithmetic blocker in `PositiveZFirstCycleBridges.lean`'s `firstCycleQ_from_S0Input`: after unfolding the Nat-valued sweep length and rewriting the supplied head equation, the proof now expands Nat casts over addition, multiplication, and powers, then uses the already-proved `hsub` identity for `(2^z-1 : Nat)` before `omega`. This addresses the reported final-frame head mismatch without changing the theorem statement or execution semantics.

The source edit is committed as one checkpoint. I could not run the local Lean preflight in this invocation because both the shell and Python execution tools returned tool-level ClientError; please test this exact module/dependency closure in your working Lean 4.36.0-rc2 environment before any CI dispatch. If `Nat.cast_pow` is not the right simplifier lemma in this Lean build, send the exact elaboration error and I will adjust the cast normalization.

The earlier reported blockers in `firstCycleTwoZeroSetup`, `firstCyclePostlude_at`, and the power lower bounds were addressed in the preceding source revision. This is still an intermediate proof draft until the complete import closure and transitive axiom audit pass.
