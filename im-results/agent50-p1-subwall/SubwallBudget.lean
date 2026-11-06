import SubwallLog
import WallCountLowerBound

set_option maxHeartbeats 2000000

namespace BB6.Agent50SubwallBudget
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent50SubwallLog BB6.Agent50TwoReset

/-- Every exact counted source inverse history whose shifted left counter is
    at or below the critical affine wall has its positive-reset budget above
    the original fixed-count dyadic envelope. -/
theorem counted_excludes_budgeted_subwall
    (n j b d m : Nat)
    (hn : 42 ≤ n)
    (hbudget : budget n j*(n+2)<2^n)
    (hcount : CountCone (14*2^n-2*n-16) 3 b d m (j+1))
    (hsub : b ≤ 4*(m+n)) : False := by
  let K : Nat := 7*2^n-n-3
  let b0 : Nat := 14*2^n-2*n-16
  have hdom : n+4≤2^n := n_plus_four_le_pow n (by omega)
  have hK : K+n+3=7*2^n := by dsimp [K]; omega
  have hroot : b0+10=2*K := by dsimp [b0,K]; omega
  have hshape :=
    (source_counted_to_reset_skeleton n K b0 b d m (j+1)
      hn hK hroot (by simpa only [b0] using hcount)).2
      (by omega : 1 ≤ j+1)
  obtain ⟨F,D,hF,hD,hsk⟩ := hshape
  have hskj : ResetSkeleton n K j m F D := by
    simpa only [Nat.add_sub_cancel_right] using hsk
  have hodd : OddCone b0 3 b d m :=
    counted_to_odd b0 3 b d m (j+1)
      (by simpa only [b0] using hcount)
  have hlog : 2^(n-m)<n :=
    source_critical_subwall_cost_logarithmic_gap n b d m
      (by omega) (by simpa only [b0] using hodd) hsub
  exact hskj.excludes_log_wall hn hK hbudget hlog

/-- Uniform all-count necessary reset lower bound throughout the entire
    genuine P1 critical left-subwall, with arbitrary inverse history length. -/
theorem source_subwall_forces_exponential_reset_count
    (n z b d m : Nat)
    (hn : 42 ≤ n) (hz : 1 ≤ z)
    (hcount : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hsub : b ≤ 4*(m+n)) :
    2^n ≤ 24^z*(n+2)^(2*z+2) := by
  have hlow : 2^n ≤ budget n (z-1)*(n+2) := by
    by_cases hle : 2^n ≤ budget n (z-1)*(n+2)
    · exact hle
    have hsmall : budget n (z-1)*(n+2) < 2^n := by omega
    have hc : CountCone (14*2^n-2*n-16) 3 b d m ((z-1)+1) := by
      simpa only [Nat.sub_add_cancel hz] using hcount
    exact False.elim
      (counted_excludes_budgeted_subwall n (z-1) b d m
        hn hsmall hc hsub)
  have hclosed : budget n (z-1)=24^z*(n+2)^(2*z+1) := by
    have h := budget_closed_form n (z-1)
    have hi : (z-1)+1=z := by omega
    have hi2 : 2*(z-1)+3=2*z+1 := by omega
    simpa only [hi,hi2] using h
  have hpow : (n+2)^(2*z+1)*(n+2)=(n+2)^(2*z+2) := by
    have hh := Nat.pow_succ (n+2) (2*z+1)
    have hi : (2*z+1)+1=2*z+2 := by omega
    simpa only [hi] using hh.symm
  calc
    2^n ≤ budget n (z-1)*(n+2) := hlow
    _ = 24^z*(n+2)^(2*z+2) := by
      rw [hclosed]
      calc
        (24^z*(n+2)^(2*z+1))*(n+2) =
          24^z*((n+2)^(2*z+1)*(n+2)) := by ac_rfl
        _ = 24^z*(n+2)^(2*z+2) := by rw [hpow]

#print axioms BB6.Agent50SubwallBudget.source_subwall_forces_exponential_reset_count

#print axioms BB6.Agent50SubwallBudget.counted_excludes_budgeted_subwall

end BB6.Agent50SubwallBudget
