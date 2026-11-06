import Arithmetic
import CountedWallStrongGateSource

namespace BB6.Agent50Subwall

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6.Agent43LastResetDraft BB6.Agent43LastResetStrength

private theorem nat_le_two_pow (n : Nat) : n ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have hp : 0 < (2:Nat)^n := Nat.pow_pos (by decide)
    omega

/-- The last positive reset outputs a large shifted left coordinate whenever
    its final counted cost does not exceed 2^n. -/
theorem source_last_reset_large_left_under_power
    (n bp dp mp t k c m : Nat)
    (hn : 14 ≤ n)
    (hpre : OddCone (14*2^n-2*n-16) 3 bp dp mp)
    (hbp : 8 ≤ bp) (hbp4 : bp%4=0) (hdp : dp%2=1)
    (hip : inverseAt bp dp t = some (k,c))
    (hkp : 2 ≤ k) (hcp : c%2=1) (htp : 1 ≤ t)
    (hm1 : mp+t+1 ≤ m) (hm : m ≤ 2^n) :
    2*2^n ≤ k+4 := by
  have hnP : n ≤ 2^n := nat_le_two_pow n
  have hP4 : 4 ≤ (2:Nat)^n := by omega
  have hroot : (14*2^n-2*n-16)+2*n+16=14*2^n := by omega
  have hmassPre := odd_cone_mass
    (14*2^n-2*n-16) 3 bp dp mp hpre
  have hp := (inverseAt_iff_power_mass bp dp t k c
    (by omega) hbp4 hdp).mp hip
  have hpowlt : (2:Nat)^0 < 2^t :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have htwo : 2 ≤ (2:Nat)^t := by
    simp only [Nat.pow_zero] at hpowlt
    omega
  have hpowBound : 2*(c+3) ≤ 2^t*(c+3) :=
    Nat.mul_le_mul_right (c+3) htwo
  have hcBound : c+n+8 ≤ 7*2^n := by omega
  have hmassIff := hp.2
  omega

/-- For any genuine counted P1 inverse history with a low-cost endpoint on
    or below the affine left wall, the last positive reset imposes a precise
    dyadic cost inequality. No restriction on the right counter. -/
theorem source_subwall_last_reset_cost_tradeoff
    (n b d m z : Nat)
    (hn : 14 ≤ n) (hz : 1 ≤ z)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hb : b ≤ 4*(m+n))
    (hm : m ≤ 2^n) :
    2^(n+2*z) ≤ 2^m*(m+n+3) := by
  obtain ⟨bp,dp,mp,zp,t,k,c,s,hpre,hzEq,hbp,hbp4,hdp,hip,hkp,hcp,htp,htail⟩ :=
    counted_last_positive_reset
      (14*2^n-2*n-16) 3 b d m z h hz
  have hodd : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
    counted_to_odd_cone _ _ _ _ _ _ hpre
  have htailFacts := upper_tail_dyadic
    (2*k-4) (c+4) (mp+t+1) b d m s htail
  have htailPow : 2^s*(b+12)=(2*k-4)+12 := htailFacts.1
  have htailCost : m=(mp+t+1)+s := htailFacts.2
  have hm1 : mp+t+1 ≤ m := by omega
  have hlarge : 2*2^n ≤ k+4 :=
    source_last_reset_large_left_under_power
      n bp dp mp t k c m hn hodd hbp hbp4 hdp hip hkp hcp htp hm1 hm
  have hprefixCost : 2*zp ≤ mp :=
    counted_cost_at_least_twice_resets _ _ _ _ _ _ hpre
  have hcost : 2*z ≤ mp+t+1 := by omega
  have hshift : (2*k-4)+12=2*(k+4) := by omega
  rw [hshift] at htailPow
  exact subwall_arithmetic n m z s (mp+t+1) k b hlarge htailPow hb hcost htailCost

#print axioms BB6.Agent50Subwall.source_last_reset_large_left_under_power
/-- All finite authentic inverse histories satisfy the last-reset obstruction
    for an arbitrary offset of the left-coordinate threshold. -/
theorem source_offset_subwall_last_reset_cost_tradeoff
    (n r b d m z : Nat)
    (hn : 14 ≤ n) (hz : 1 ≤ z)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hb : b ≤ 4*(m+n+r))
    (hm : m ≤ 2^n) :
    2^(n+2*z) ≤ 2^m*(m+n+r+3) := by
  obtain ⟨bp,dp,mp,zp,t,k,c,s,hpre,hzEq,hbp,hbp4,hdp,hip,hkp,hcp,htp,htail⟩ :=
    counted_last_positive_reset
      (14*2^n-2*n-16) 3 b d m z h hz
  have hodd : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
    counted_to_odd_cone _ _ _ _ _ _ hpre
  have htailFacts := upper_tail_dyadic
    (2*k-4) (c+4) (mp+t+1) b d m s htail
  have htailPow : 2^s*(b+12)=(2*k-4)+12 := htailFacts.1
  have htailCost : m=(mp+t+1)+s := htailFacts.2
  have hm1 : mp+t+1 ≤ m := by omega
  have hlarge : 2*2^n ≤ k+4 :=
    source_last_reset_large_left_under_power
      n bp dp mp t k c m hn hodd hbp hbp4 hdp hip hkp hcp htp hm1 hm
  have hprefixCost : 2*zp ≤ mp :=
    counted_cost_at_least_twice_resets _ _ _ _ _ _ hpre
  have hcost : 2*z ≤ mp+t+1 := by omega
  have hshift : (2*k-4)+12=2*(k+4) := by omega
  rw [hshift] at htailPow
  exact subwall_offset_arithmetic n m z s (mp+t+1) k b r
    hlarge htailPow hb hcost htailCost

/-- The width used for genuine n=16q+2 even-right exits is within this
    theorem's domain whenever the authentic small-left condition is available. -/
theorem source_small_left_exit_cost_tradeoff
    (q b d m z : Nat)
    (hq : 1 ≤ q) (hz : 1 ≤ z)
    (h : CountCone (14*2^(16*q+2)-2*(16*q+2)-16) 3 b d m z)
    (hb : b ≤ 4*m+192*q+40)
    (hm : m ≤ 2^(16*q+2)) :
    2^(16*q+2+2*z) ≤ 2^m*(m+48*q+13) := by
  have hn : 14 ≤ 16*q+2 := by omega
  have hw : b ≤ 4*(m+(16*q+2)+(32*q+8)) := by omega
  have result := source_offset_subwall_last_reset_cost_tradeoff
    (16*q+2) (32*q+8) b d m z hn hz h hw hm
  have hnum : m+(16*q+2)+(32*q+8)+3 = m+48*q+13 := by omega
  simpa only [hnum] using result

#print axioms BB6.Agent50Subwall.source_subwall_last_reset_cost_tradeoff
#print axioms BB6.Agent50Subwall.source_offset_subwall_last_reset_cost_tradeoff
#print axioms BB6.Agent50Subwall.source_small_left_exit_cost_tradeoff

end BB6.Agent50Subwall
