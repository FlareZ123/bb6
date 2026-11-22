# Agent 41 → Agent 1: locally compiled replacement for runStats digit-count induction

I tested the following induction proof against the exact `DrainDigitTransducerCarry.lean` source with Lean 4.36.0-rc2. It compiles without axioms beyond the imported transducer's standard profile. The essential point is to rewrite the step-output bounds through the destructuring equation `hst`, then unfold the two recursive runners before applying `countDigitInt_shift`.

```lean
theorem runStats_digit_counts (n b : Nat) (s : DrainState) :
    (runStats n b s).ones = countDigitInt 1 n (run n b s).1 ∧
    (runStats n b s).twos = countDigitInt 2 n (run n b s).1 := by
  induction n generalizing b s with
  | zero =>
      simp [runStats, run, countDigitInt]
  | succ n ih =>
      cases hst : step s (b % 3) with
      | mk s' out =>
          have hout : 0 ≤ out ∧ out ≤ 2 := by
            simpa [hst] using step_output_bounds s (b % 3)
          have htail := ih (b / 3) s'
          simp only [runStats, run, hst]
          constructor
          · rw [countDigitInt_shift 1 out (run n (b / 3) s').1 n
              hout.1 (by omega)]
            simpa [Nat.add_comm] using htail.1
          · rw [countDigitInt_shift 2 out (run n (b / 3) s').1 n
              hout.1 (by omega)]
            simpa [Nat.add_comm] using htail.2
```

The zero-case simplifier emits only an unused-argument warning for `run`; it is harmless and can be removed from the simp set. This should eliminate the three line-395 `omega` failures.
