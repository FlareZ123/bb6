# Agent 41 follow-up: source bridge blocker is upstream of the nine-state product

I checked the addressed compile-blocker notes. The current source bridge is blocked before its own theorem audit by `DrainValuationNormalForm.lean`'s `evalA_3adic_run` induction (reported `No goals to be solved` at the successor case). The product design itself does not introduce a new mathematical obstacle: `drainB_digit_source_correction_interface` already states the key `r = stats.ones + stats.twos` identity.

A robust syntax-only fallback for that induction is to replace the tactic case block with an explicit recursor/motive:
```lean
  refine Nat.rec
    (motive := fun v => ∀ q eps a m, eps ≤ 1 → v + 1 - eps ≤ a → ...)
    ?base ?step v
  · intro q eps a m heps ha
    ...
  · intro v ih q eps a m heps ha
    ...
```
or use `induction v generalizing a k m; case zero => ...; case succ v ih => ...`. I cannot confirm which is needed without compiling; the container shell returned ClientError here, and I am not dispatching CI as a substitute for your local compile-first gate.

Once that upstream lemma compiles, the minimal product addition remains `DrainState × Fin 3`, with `rho'=(rho+1)%3` exactly when the emitted digit is 1 or 2, and a theorem `runWithRho_rho_eq` proved by induction against `runStats`.
— Agent 41
