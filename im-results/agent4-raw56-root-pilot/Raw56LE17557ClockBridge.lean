import Raw56LE17557TimeCocycle

/-!
  A precise quantitative missing-proof interface for the 17557 dyadic
  checkpoint clock. The abstract local triad cost cocycle is already
  checked in Raw56LE17557TimeCocycle.

  The hypotheses below are NOT yet original-source all-epoch invariants.
  Finite blank-tape replay satisfies them through epoch 8. Proving them
  for every rank in the authentic zipper semantics would yield the exact
  primitive-step epoch recurrence, without needing a separate giant
  primitive-step induction.
-/

namespace BB6.Agent4Raw56LE17557ClockBridge
open BB6.Agent4Raw56LE17557TimeCocycle

/-- All-time clock reduction: the balanced A/B action word, the number
    of rightmost-one-run events, and the single third-run-length sum
    completely determine the 17557 high/low epoch duration relation.

    Here n is the low epoch index (n >= 2 for the actual machine);
    sums range over the individual *realized* low triad events and
    highTime is the substitution-transported high triad cost. -/
theorem epoch_clock_of_observables (xs : List Triad) (n : Nat)
    (hA : (xs.map isA).sum = 2*3^(n-2))
    (hB : (xs.map isB).sum = 2*3^(n-2))
    (hFA : (xs.map finalA).sum = 2^(n-2))
    (hFB : (xs.map finalB).sum = 2^(n-2))
    (hC : (xs.map thirdRun).sum +
      32*3^(n-2) + 2^(n-2) = 3*4^n) :
    (xs.map highTime).sum =
      2*(xs.map lowTime).sum +
      24*4^n + 48*3^(n-2) := by
  rw [word_time_cocycle, sum_excess_decompose,
      hA, hB, hFA, hFB]
  omega

/-- Same formula in the conventional epoch-index notation:
    48 * 3^(n-2) = 16 * 3^(n-1) for n>=2. -/
theorem epoch_clock_classical_form (xs : List Triad) (n : Nat)
    (hn : 2 ≤ n)
    (hA : (xs.map isA).sum = 2*3^(n-2))
    (hB : (xs.map isB).sum = 2*3^(n-2))
    (hFA : (xs.map finalA).sum = 2^(n-2))
    (hFB : (xs.map finalB).sum = 2^(n-2))
    (hC : (xs.map thirdRun).sum +
      32*3^(n-2) + 2^(n-2) = 3*4^n) :
    (xs.map highTime).sum =
      2*(xs.map lowTime).sum +
      24*4^n + 16*3^(n-1) := by
  have h := epoch_clock_of_observables xs n hA hB hFA hFB hC
  have hpow : 3^(n-1) = 3^(n-2)*3 := by
    have eqn : n-1 = (n-2)+1 := by omega
    rw [eqn, Nat.pow_succ]
  rw [h, hpow]
  omega

#print axioms epoch_clock_of_observables
#print axioms epoch_clock_classical_form
end BB6.Agent4Raw56LE17557ClockBridge
