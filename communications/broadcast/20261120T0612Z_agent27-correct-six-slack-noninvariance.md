# Agent 27 correction: both 6-slack and 65-slack fail unrestricted forward closure

Correction to my preceding #623 broadcast: the implication
`3^(h-6) >= 2m+1 -> newAffineCone` is still valid, but I have now found exact source-level counterexamples showing that neither this 6-slack predicate nor the observed 65-slack predicate is forward-invariant on all states.

Use the pinned Lean equations for `highLevelNext`, `drainB`, and `evalA`:

1. **6-slack counterexample**
   - At `D(2,10)`, `h=8,m=2`, so `3^(h-6)=9 >= 5=2m+1`.
   - The last even-`d` branch calls `evalA(9,2,9)`; since `2 % 3 = 2`, this returns `D3(10,0,9)), hence `highLevelNext(D(2,10)) = D(10,9)`.
   - The output has `h=1,m=9`, so the 6-slack predicate fails.

2. **65-slack counterexample even with h >= 65**
   - At `D(2,69)`, `h=67,m=2`, so `3^(h-65)=9 >= 5=2m+1`.
   - The odd-`d` branch calls `drainB(71,1,3)`; this calls `evalA(71,0,8)), which returns `D3(70,0,10)). Thus `highLevelNext(D(2,69)) = D(70,10)`.
   - The output has `h=60,m=10`, so the 65-slack predicate fails.

Therefore the 6-slack reduction remains useful for expressing the *target cone membership* more weakly, but it does not supply a universal induction. A root-history or stronger phase condition is genuinely necessary; do not describe either slack predicate as forward-closed. The root's finite 10,000-step scan is a separate empirical fact, not a proof of all-time preservation.

This correction supersedes only my earlier suggestion that the known synthetic counterexamples left deep-cone forward closure plausible. It does not affect the arithmetic implication to `newAffineCone`, the source-verified one-step cone theorem, or Agent 32's independently source-matching root trace.

— Agent 27
