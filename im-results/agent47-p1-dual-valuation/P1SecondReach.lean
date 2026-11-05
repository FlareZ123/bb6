import P1SecondFan
import P1ResidualReach

namespace BB6.P1SecondFan
open BB6.Agent45TwoRoot
open BB6.P1Reduction

/-- For every odd q, blank reachability of the second original P1 critical
    feeder implies reachability of one of two exact sparse earlier feeders.
    The complete original GAncestor trichotomy and the positive-even-right
    power-shape theorem exclude every other source predecessor. -/
theorem odd_second_reach_requires_two (q : Nat) (hq : 1≤q) (hodd : q%2=1)
    (hr : BB6.Agent1.Reach (6*u2 q-2) (2*u2 q+5)) :
    BB6.Agent1.Reach (24*w2 q-4) (40*w2 q+13) ∨
    BB6.Agent1.Reach (44*w2 q) (20*w2 q+7) := by
  have hrelation := odd_w2_identity q hq hodd
  have hu : 3 ≤ u2 q := by
    simpa only [u2] using BB6.P1DualValuation.feeder_u_lower q hq
  have hno : ∀ z, ¬GAncestor (6*u2 q-2) (2*u2 q+5) z 1 := by
    intro z hz
    rcases odd_second_inverse_three_source q z 1 hq hodd hz with
      ⟨hk,hc⟩ | ⟨hk,hc⟩ | ⟨hk,hc⟩ <;> omega
  obtain ⟨k,c,hanc,hc,hreach⟩ :=
    BB6.Agent50P1.positive_G_feeder (6*u2 q-2) (2*u2 q+5)
      (by omega) (by omega) (by omega) hno hr
  rcases odd_second_inverse_three_source q k c hq hodd hanc with
    ⟨hk,hc'⟩ | ⟨hk,hc'⟩ | ⟨hk,hc'⟩
  · left
    have heq1 : 2*k-4 = 24*w2 q-4 := by omega
    have heq2 : c+4=40*w2 q+13 := by omega
    simpa only [heq1,heq2] using hreach
  · right
    have heq1 : 2*k-4 = 44*w2 q := by omega
    have heq2 : c+4=20*w2 q+7 := by omega
    simpa only [heq1,heq2] using hreach
  · have heq1 : 2*k-4 = 54*w2 q+2 := by omega
    have heq2 : c+4=10*w2 q+4 := by omega
    rw [heq1,heq2] at hreach
    obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape
      (54*w2 q+2) (10*w2 q+4) hreach
      (by omega) (by omega) (by omega)
    exact False.elim ((odd_last_power_gap q j hq hodd) (by omega))

#print axioms odd_second_reach_requires_two
end BB6.P1SecondFan
