import SubwallNear
import ZeroArithmetic

namespace BB6.Agent50SubwallAllCount

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail
open BB6.Agent50SubwallLog BB6.Agent50SubwallZero
open BB6.Agent50TwoReset BB6.Agent50SubwallNear

/-- The no-positive-reset case cannot enter the left subwall at cost
    <= n. Dyadic divisibility and source logarithmic gap conflict. -/
theorem source_zero_reset_subwall_cost_above_n
    (n b d m : Nat) (hn : 62 ≤ n)
    (hc : CountCone (14*2^n-2*n-16) 3 b d m 0)
    (hsub : b ≤ 4*(m+n)) : n < m := by
  by_cases hm : m ≤ n
  · obtain ⟨s,htail⟩ := (cone_shape _ _ b d m 0 hc).1 rfl
    have hfact := upper_tail_dyadic
      (14*2^n-2*n-16) 3 0 b d m s htail
    have hcost : m=s := by omega
    have hPow : 2^m*(b+12)=14*2^n-2*n-16+12 := by
      simpa only [hcost] using hfact.1
    have hdom : n+4 ≤ 2^n := n_plus_four_le_pow n (by omega)
    have hrootEq : 2^m*(b+12)+2*(n+2)=14*2^n := by
      rw [hPow]
      omega
    have hPowSmall : 2^m ≤ 2*(n+2) :=
      zero_arith n m b hm hrootEq
    have hOdd : OddCone (14*2^n-2*n-16) 3 b d m :=
      counted_to_odd _ _ _ _ _ _ hc
    have hLog : 2^(n-m)<n :=
      source_critical_subwall_cost_logarithmic_gap n b d m
        (by omega) hOdd hsub
    have hnum : 2*n*(n+2)<2^n :=
      quadratic_below_power n (octic_growth n hn)
    have hPn : 2^n=2^m*2^(n-m) := by
      calc
        2^n=2^(m+(n-m)) := by congr 1; omega
        _ = 2^m*2^(n-m) := Nat.pow_add 2 m (n-m)
    have hpStrict : 2^n < 2^m*n := by
      rw [hPn]
      exact Nat.mul_lt_mul_of_pos_left hLog (Nat.pow_pos (by decide))
    have hpUpper : 2^m*n ≤ 2*(n+2)*n :=
      Nat.mul_le_mul_right n hPowSmall
    have heq : 2*(n+2)*n=2*n*(n+2) := by ac_rfl
    omega
  · omega

/-- The exact source P1 left-subwall is inaccessible at cost <=n+z for all
    n>=148 and every counted inverse word, including zero-reset histories. -/
theorem source_subwall_allcount_cost_above_n_plus_resets
    (n b d m z : Nat) (hn : 148 ≤ n)
    (hc : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hsub : b ≤ 4*(m+n)) :
    n+z < m := by
  by_cases hz : z=0
  · have hzero : CountCone (14*2^n-2*n-16) 3 b d m 0 := by
      simpa only [hz] using hc
    have hh := source_zero_reset_subwall_cost_above_n
      n b d m (by omega) hzero hsub
    omega
  · have hzpos : 1 ≤ z := by omega
    exact source_subwall_positive_reset_cost_above_n_plus_resets
      n b d m z hn hzpos hc hsub

#print axioms BB6.Agent50SubwallAllCount.source_zero_reset_subwall_cost_above_n
#print axioms BB6.Agent50SubwallAllCount.source_subwall_allcount_cost_above_n_plus_resets

end BB6.Agent50SubwallAllCount
