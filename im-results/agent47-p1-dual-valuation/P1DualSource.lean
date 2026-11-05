import P1TwoSector
import GInverse
import P1DualValuation

namespace BB6.P1DualSource
open BB6.Agent45TwoRoot
open BB6.P1Reduction

/-- The authentic Agent45 second feeder's exact shifted GAncestor output. -/
theorem second_shift_source (q : Nat) (hq : 1≤q) :
    (2*u2 q+5)+(6*u2 q-2)/2+3 = BB6.P1DualValuation.shift q := by
  have hu : 3 ≤ u2 q := by
    simpa only [u2] using BB6.P1DualValuation.feeder_u_lower q hq
  have hformula : (2*u2 q+5)+(6*u2 q-2)/2+3 = 5*u2 q+7 := by
    omega
  rw [hformula]
  simpa only [u2] using BB6.P1DualValuation.second_feeder_shift q hq

/-- For odd q, every complete G-inverse candidate of the true second
    P1 critical feeder has inverse nesting exponent at most two. -/
theorem odd_second_feeder_inverse_depth (q k c : Nat)
    (hq : 1≤q) (hodd : q%2=1)
    (h : GAncestor (6*u2 q-2) (2*u2 q+5) k c) :
    ∃ t : Nat, t ≤ 2 ∧
      (2*u2 q+5)+(6*u2 q-2)/2+3 = 2^t*(c+3) := by
  obtain ⟨t,he⟩ := GAncestor_power (6*u2 q-2) (2*u2 q+5) k c h
  have hdvd : 2^t ∣ BB6.P1DualValuation.shift q := by
    rw [←second_shift_source q hq,he]
    exact ⟨c+3,rfl⟩
  have hnot : ¬ 8 ∣ BB6.P1DualValuation.shift q :=
    (BB6.P1DualValuation.second_feeder_odd_exact q hq hodd).2
  have hbound : t≤2 := by
    by_cases hh : t≤2
    · exact hh
    · have h3 : 3≤t := by omega
      have h8 : 8 ∣ 2^t := by
        simpa using (Nat.pow_dvd_pow 2 h3 : 2^3 ∣ 2^t)
      exact False.elim (hnot (Nat.dvd_trans h8 hdvd))
  exact ⟨t,hbound,he⟩

#print axioms second_shift_source
#print axioms odd_second_feeder_inverse_depth
end BB6.P1DualSource
