import OffsetBudget
import OffsetNumeric
import SubwallNear

namespace BB6.Agent50OffsetNear

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6.Agent43LastResetDraft BB6.Agent43LastResetStrength
open BB6.Agent50OffsetBudget BB6.Agent50OffsetNumeric

/-- For an arbitrary offset r, near-cost inverse feeders must have a
    logarithmically small number of positive-depth reset transitions. -/
theorem source_offset_near_cost_has_reset_bound
    (n r b d m z : Nat)
    (hn : 14 ≤ n) (hz : 1 ≤ z)
    (hc : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hsub : b ≤ 4*(m+n+r))
    (hm : m ≤ n+z) :
    3*2^z ≤ 2*(m+n+r+3) := by
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
  have hsubNorm : b+12 ≤ 4*(m+n+r+3) := by omega
  have hshift : (2*k-4)+12=2*(k+4) := by omega
  rw [hshift] at htailPow
  have htailBound : 2*(k+4) ≤ 2^s*(4*(m+n+r+3)) := by
    rw [←htailPow]
    exact Nat.mul_le_mul_left (2^s) hsubNorm
  have hscale :
      2^s*(4*(m+n+r+3))=2*(2^s*(2*(m+n+r+3))) := by
    calc
      _ = 2^s*((2*2)*(m+n+r+3)) := by
        rw [show (4:Nat)=2*2 by decide]
      _ = 2*(2^s*(2*(m+n+r+3))) := by ac_rfl
  rw [hscale] at htailBound
  have hpositive : 3*2^n ≤ 2^s*(2*(m+n+r+3)) := by omega
  have hsBound : s+z ≤ n := by omega
  have hpowMono : 2^s ≤ 2^(n-z) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpowEq : 2^n = 2^(n-z)*2^z := by
    calc
      2^n = 2^((n-z)+z) := by congr 1; omega
      _ = 2^(n-z)*2^z := Nat.pow_add 2 (n-z) z
  have hpMul :
      2^(n-z)*(3*2^z) ≤ 2^(n-z)*(2*(m+n+r+3)) := by
    calc
      2^(n-z)*(3*2^z) = 3*2^n := by rw [hpowEq]; ac_rfl
      _ ≤ 2^s*(2*(m+n+r+3)) := hpositive
      _ ≤ 2^(n-z)*(2*(m+n+r+3)) :=
        Nat.mul_le_mul_right (2*(m+n+r+3)) hpowMono
  exact Nat.le_of_mul_le_mul_left hpMul (Nat.pow_pos (by decide))

/-- At n>=512 and arbitrary r<=2n+4, all authentic positive-reset
    subwall histories exceed cost n+z. -/
theorem source_offset_positive_cost_above_n_plus_resets
    (n r b d m z : Nat)
    (hn : 512 ≤ n) (hr : r ≤ 2*n+4) (hz : 1 ≤ z)
    (hc : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hsub : b ≤ 4*(m+n+r)) : n+z < m := by
  by_cases hm : m ≤ n+z
  · have hmin := counted_cost_at_least_twice_resets
      (14*2^n-2*n-16) 3 b d m z hc
    have hzle : z ≤ n := by omega
    have hnear : 3*2^z ≤ 2*(m+n+r+3) :=
      source_offset_near_cost_has_reset_bound
        n r b d m z (by omega) hz hc hsub hm
    have hgate : 3*2^z ≤ 8*n+2*z+14 := by omega
    have hzshell : 2^z ≤ 4*n := by omega
    have hnum : 3*24^z*(n+2)^(2*z+2) < 2^n :=
      shell_large_numeric_triple n z hn hzshell
    have hreset : 2^n ≤ 24^z*(n+2)^(2*z+1)*(n+r) :=
      source_offset_subwall_forces_exponential_reset_count
        n r z b d m (by omega) hz hc hsub
    have hsmallwidth : n+r ≤ 3*(n+2) := by omega
    have hlocal :
        (n+2)^(2*z+1)*(n+r) ≤
        (n+2)^(2*z+1)*(3*(n+2)) :=
      Nat.mul_le_mul_left ((n+2)^(2*z+1)) hsmallwidth
    have hrearr :
        (n+2)^(2*z+1)*(3*(n+2))=3*(n+2)^(2*z+2) := by
      rw [show 2*z+2=(2*z+1)+1 by omega, Nat.pow_succ]
      ac_rfl
    have hbound :
        24^z*(n+2)^(2*z+1)*(n+r) ≤
          3*24^z*(n+2)^(2*z+2) := by
      calc
        _ ≤ 24^z*((n+2)^(2*z+1)*(3*(n+2))) :=
          Nat.mul_le_mul_left (24^z) hlocal
        _ = 3*24^z*(n+2)^(2*z+2) := by rw [hrearr]; ac_rfl
    omega
  · omega

#print axioms BB6.Agent50OffsetNear.source_offset_near_cost_has_reset_bound
#print axioms BB6.Agent50OffsetNear.source_offset_positive_cost_above_n_plus_resets

end BB6.Agent50OffsetNear
