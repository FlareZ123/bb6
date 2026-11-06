import SubwallBudget
import CountedWallStrongGateSource
import NumericBridge148

namespace BB6.Agent50SubwallNear

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6.Agent43LastResetDraft BB6.Agent43LastResetStrength
open BB6.Agent43Numeric148 BB6.Agent50SubwallBudget

/-- Original inverse source: near-cost critical endpoints below the affine
    wall force a short positive-reset count, regardless of inverse depth. -/
theorem source_subwall_near_cost_has_reset_bound
    (n b d m z : Nat)
    (hn : 14 ≤ n) (hz : 1 ≤ z)
    (hc : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hsub : b ≤ 4*(m+n))
    (hm : m ≤ n+z) :
    3*2^z ≤ 2*(m+n+3) := by
  obtain ⟨bp,dp,mp,zp,t,k,c,s,hpre,hzEq,hbp,hbp4,hdp,hip,hkp,hcp,htp,htail⟩ :=
    counted_last_positive_reset
      (14*2^n-2*n-16) 3 b d m z hc hz
  have hodd : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
    counted_to_odd_cone _ _ _ _ _ _ hpre
  have htailFacts := upper_tail_dyadic
    (2*k-4) (c+4) (mp+t+1) b d m s htail
  have htailPow : 2^s*(b+12)=(2*k-4)+12 := htailFacts.1
  have htailCost : m=(mp+t+1)+s := htailFacts.2
  have hprefixCost : 2*zp ≤ mp :=
    counted_cost_at_least_twice_resets _ _ _ _ _ _ hpre
  have hm1 : mp+t+1 ≤ m := by omega
  have hmz : 2*z ≤ mp+t+1 := by omega
  have hlarge : 3*2^n ≤ k+4 :=
    source_last_positive_large_left n bp dp mp t k c m z
      hn hz hodd hbp hbp4 hdp hip hkp hcp htp hm1 hmz hm
  have hsubNorm : b+12 ≤ 4*(m+n+3) := by omega
  have hshift : (2*k-4)+12=2*(k+4) := by omega
  rw [hshift] at htailPow
  have htailBound : 2*(k+4) ≤ 2^s*(4*(m+n+3)) := by
    rw [←htailPow]
    exact Nat.mul_le_mul_left (2^s) hsubNorm
  have hscale : 2^s*(4*(m+n+3))=2*(2^s*(2*(m+n+3))) := by
    calc
      _ = 2^s*((2*2)*(m+n+3)) := by
        rw [show (4:Nat)=2*2 by decide]
      _ = 2*(2^s*(2*(m+n+3))) := by ac_rfl
  rw [hscale] at htailBound
  have hpositive : 3*2^n ≤ 2^s*(2*(m+n+3)) := by omega
  have hsBound : s+z ≤ n := by omega
  have hpowMono : 2^s ≤ 2^(n-z) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpowEq : 2^n = 2^(n-z)*2^z := by
    calc
      2^n = 2^((n-z)+z) := by congr 1; omega
      _ = 2^(n-z)*2^z := Nat.pow_add 2 (n-z) z
  have hpMul :
      2^(n-z)*(3*2^z) ≤ 2^(n-z)*(2*(m+n+3)) := by
    calc
      2^(n-z)*(3*2^z) = 3*2^n := by rw [hpowEq]; ac_rfl
      _ ≤ 2^s*(2*(m+n+3)) := hpositive
      _ ≤ 2^(n-z)*(2*(m+n+3)) :=
        Nat.mul_le_mul_right (2*(m+n+3)) hpowMono
  exact Nat.le_of_mul_le_mul_left hpMul (Nat.pow_pos (by decide))

/-- For all n>=148, a genuine critical subwall history with one or more
    positive resets must cost strictly more than n plus its reset count. -/
theorem source_subwall_positive_reset_cost_above_n_plus_resets
    (n b d m z : Nat) (hn : 148 ≤ n) (hz : 1 ≤ z)
    (hc : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hsub : b ≤ 4*(m+n)) :
    n+z < m := by
  by_cases hm : m ≤ n+z
  · have hmin := counted_cost_at_least_twice_resets
      (14*2^n-2*n-16) 3 b d m z hc
    have hzle : z ≤ n := by omega
    have hstrong : 3*2^z ≤ 2*(m+n+3) :=
      source_subwall_near_cost_has_reset_bound n b d m z
        (by omega) hz hc hsub hm
    have hgate : 3*2^z ≤ 4*n+2*z+6 := by omega
    have hnumeric : 24^z*(n+2)^(2*z+2) < 2^n :=
      universal_numeric_gap_148 n z hn hzle hgate
    have hreset : 2^n ≤ 24^z*(n+2)^(2*z+2) :=
      source_subwall_forces_exponential_reset_count
        n z b d m (by omega) hz hc hsub
    omega
  · omega

#print axioms BB6.Agent50SubwallNear.source_subwall_near_cost_has_reset_bound
#print axioms BB6.Agent50SubwallNear.source_subwall_positive_reset_cost_above_n_plus_resets

end BB6.Agent50SubwallNear
