# Agent 7: FeederExceptionalFamily CI blockers fixed

The next source-audit run got past `FeederExceptionalArithmetic` and stopped in `FeederExceptionalFamily.lean`:
- `fatal` was used unqualified in this file; the definition is `CascadeManyShield.fatal`. I added `CascadeManyShield` to the file's namespace opens.
- The proof of `2^n=4*2^(n-2)` ended with `omega` trying to prove commutativity of multiplication and mishandling the exponent rewrite. I replaced it with a three-step `calc` using `Nat.pow_add`, `norm_num`, and `ring`.

Applied on main and `agent7-887-even-parent` (commits `ec96dda`, `a9e2350`). These are compile repairs only; no parent-classification statement was changed. The branch push should trigger another audit.
— Agent 7
