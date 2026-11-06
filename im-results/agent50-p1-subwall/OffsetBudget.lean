import OffsetLog
import SubwallBudget

set_option maxHeartbeats 2000000

namespace BB6.Agent50OffsetBudget
open BB6.Agent28 BB6.Agent1Quarter
open BB6.Agent50OffsetLog BB6.Agent50TwoReset

/-- The existing exact positive-reset grammar controls arbitrary-offset
    below-wall histories, with the natural larger multiplier n+r. -/
theorem counted_excludes_budgeted_offset_subwall
    (n r j b d m : Nat) (hn : 42 ≤ n)
    (hbudget : budget n j*(n+r)<2^n)
    (hcount : CountCone (14*2^n-2*n-16) 3 b d m (j+1))
    (hsub : b ≤ 4*(m+n+r)) : False := by
  let K : Nat := 7*2^n-n-3
  let b0 : Nat := 14*2^n-2*n-16
  have hdom : n+4≤2^n :=
    BB6.Agent50SubwallLog.n_plus_four_le_pow n (by omega)
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
  have hlog : 2^(n-m)<n+r :=
    source_critical_offset_logarithmic_gap n r b d m
      (by omega) (by simpa only [b0] using hodd) hsub
  have hfac : 1 ≤ n+r := by omega
  have hbudLe : budget n j ≤ budget n j*(n+r) := by
    have hh := Nat.mul_le_mul_left (budget n j) hfac
    simpa only [Nat.mul_one] using hh
  have hsmall : budget n j<2^n := by omega
  obtain ⟨N,C,hN,hNbound,hC,hdef,hbalance,hcostBound⟩ :=
    (hskj.toResetChain hn hK).invariant hn hK hsmall
  have hm : m<n := by
    by_cases hcase : m<n
    · exact hcase
    have hnm : n≤m := by omega
    have hp : 2^n≤2^m := Nat.pow_le_pow_right (by decide) hnm
    omega
  have hP : 2^n=2^m*2^(n-m) := by
    calc
      2^n=2^(m+(n-m)) := by congr 1; omega
      _=2^m*2^(n-m) := Nat.pow_add 2 m (n-m)
  have hmul : 2^m*2^(n-m)<2^m*(n+r) :=
    Nat.mul_lt_mul_of_pos_left hlog (Nat.pow_pos (by decide))
  have hbudmul : 2^m*(n+r) ≤ budget n j*(n+r) :=
    Nat.mul_le_mul_right (n+r) hcostBound
  omega

/-- Source-connected necessary polynomial lower bound on arbitrary-offset
    subwall reset counts, for unbounded total cost and all finite histories. -/
theorem source_offset_subwall_forces_exponential_reset_count
    (n r z b d m : Nat)
    (hn : 42 ≤ n) (hz : 1 ≤ z)
    (hcount : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hsub : b ≤ 4*(m+n+r)) :
    2^n ≤ 24^z*(n+2)^(2*z+1)*(n+r) := by
  have hlow : 2^n ≤ budget n (z-1)*(n+r) := by
    by_cases hle : 2^n ≤ budget n (z-1)*(n+r)
    · exact hle
    have hsmall : budget n (z-1)*(n+r)<2^n := by omega
    have hc : CountCone (14*2^n-2*n-16) 3 b d m ((z-1)+1) := by
      simpa only [Nat.sub_add_cancel hz] using hcount
    exact False.elim
      (counted_excludes_budgeted_offset_subwall
        n r (z-1) b d m hn hsmall hc hsub)
  have hclosed : budget n (z-1)=24^z*(n+2)^(2*z+1) := by
    have h := budget_closed_form n (z-1)
    have hi : (z-1)+1=z := by omega
    have hi2 : 2*(z-1)+3=2*z+1 := by omega
    simpa only [hi,hi2] using h
  calc
    2^n ≤ budget n (z-1)*(n+r) := hlow
    _ = 24^z*(n+2)^(2*z+1)*(n+r) := by rw [hclosed]

/-- The necessary P1 even-exit small-left width gives a uniform all-reset
    polynomial obstruction for every q>=3 in the n=16q+2 family. -/
theorem source_q_small_left_exit_forces_reset_count
    (q z b d m : Nat) (hq : 3 ≤ q) (hz : 1 ≤ z)
    (h : CountCone (14*2^(16*q+2)-2*(16*q+2)-16) 3 b d m z)
    (hb : b ≤ 4*m+192*q+40) :
    2^(16*q+2) ≤ 24^z*(16*q+4)^(2*z+1)*(48*q+10) := by
  have hn : 42 ≤ 16*q+2 := by omega
  have hw : b ≤ 4*(m+(16*q+2)+(32*q+8)) := by omega
  have hqbound := source_offset_subwall_forces_exponential_reset_count
    (16*q+2) (32*q+8) z b d m hn hz h hw
  have hbase : (16*q+2)+2=16*q+4 := by omega
  have hmult : (16*q+2)+(32*q+8)=48*q+10 := by omega
  simpa only [hbase, hmult] using hqbound

#print axioms BB6.Agent50OffsetBudget.counted_excludes_budgeted_offset_subwall
#print axioms BB6.Agent50OffsetBudget.source_offset_subwall_forces_exponential_reset_count
#print axioms BB6.Agent50OffsetBudget.source_q_small_left_exit_forces_reset_count

end BB6.Agent50OffsetBudget
