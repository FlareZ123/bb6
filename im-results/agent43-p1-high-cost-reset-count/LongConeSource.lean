import PracticalSource
import LagChecker
import LagMicro

namespace BB6.Agent43LongCone
open BB6.Agent1Quarter
open BB6.P1CarryExact (criticalLeft source_to_micro)
open BB6.Agent9FirstReturn (practicalCut practical_reset_crossing reachableThreshold reachable_reset_has_long_cone)
open BB6.Agent45.DelayedCarry (Trace Covered micro_trace no_trace_of_empty)

/-- A delayed-carry cover with no survivors bounds every authentic odd-cone
    history, with no additional left- or right-coordinate margin check. -/
theorem oddcone_cost_lt_of_empty_lag (n s b d m : Nat)
    (hn : 14 ≤ n) (he : n % 2 = 0) (hs : 1 ≤ s)
    (hz : Covered n s []) (hc : OddCone (criticalLeft n) 3 b d m) :
    m < n+s := by
  by_cases hm : n+s ≤ m
  · have hM := source_to_micro n b d m hn hc
    obtain ⟨B,a,ht,_,_⟩ := micro_trace n m _ _ hn he hM (by omega)
    exact False.elim (no_trace_of_empty n s hs hz m B a hm ht)
  · omega

/-- Source extinction alone suffices up to the practical long-cone cutoff.
    The previous margin-based gate remains useful for later extinctions. -/
theorem critical_reset_no_reach_of_short_lag (n s : Nat)
    (hn : 8000 ≤ n) (he : n % 2 = 0) (hs : 1 ≤ s)
    (hcut : n+s ≤ practicalCut n+1) (hz : Covered n s []) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro hr
  obtain ⟨b,d,m,hc,_,hm,_⟩ := practical_reset_crossing n hn he hr
  have hlt := oddcone_cost_lt_of_empty_lag n s b d m (by omega) he hs hz hc
  omega

/-- Arbitrary fixed linear horizons, subject to the effective renewal
    threshold. The long-cone theorem supplies the margin argument once,
    universally; an individual extinction certificate need not repeat it. -/
theorem critical_reset_no_reach_of_linear_lag (h n s : Nat)
    (hn : reachableThreshold h ≤ n) (he : n % 2 = 0) (hs : 1 ≤ s)
    (hcut : n+s ≤ h*n+1) (hz : Covered n s []) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  have hn' : 14 ≤ n := by
    have ht := Nat.le_max_left 8000 (BB6.Agent9Renewal.smallThreshold (h+2) (6*h+46) (h+6) 1)
    change max 8000 (BB6.Agent9Renewal.smallThreshold (h+2) (6*h+46) (h+6) 1) ≤ n at hn
    omega
  intro hr
  obtain ⟨b,d,m,hc,_,hm⟩ := reachable_reset_has_long_cone h n hn he hr
  have hlt := oddcone_cost_lt_of_empty_lag n s b d m hn' he hs hz hc
  omega

/-- A still weaker certificate obligation: forbid only actual trace lengths
    in the proved first-crossing window, even if other layers survive. -/
theorem critical_reset_no_reach_of_crossing_trace (n : Nat)
    (hn : 8000 ≤ n) (he : n % 2 = 0)
    (hz : ∀ m B a, practicalCut n < m → m ≤ practicalCut n+n+2 →
      ¬ Trace n m B a) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro hr
  obtain ⟨b,d,m,hc,_,hm,hupper⟩ := practical_reset_crossing n hn he hr
  have hM := source_to_micro n b d m (by omega) hc
  obtain ⟨B,a,ht,_,_⟩ := micro_trace n m _ _ (by omega) he hM (by omega)
  exact hz m B a hm hupper ht

#print axioms oddcone_cost_lt_of_empty_lag
#print axioms critical_reset_no_reach_of_short_lag
#print axioms critical_reset_no_reach_of_linear_lag
#print axioms critical_reset_no_reach_of_crossing_trace
end BB6.Agent43LongCone
