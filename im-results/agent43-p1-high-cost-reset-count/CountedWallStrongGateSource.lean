import LastResetStrengthSource

namespace BB6.Agent43WallStrongGate

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6.Agent43LastResetDraft BB6.Agent43LastResetStrength

/-- A source-connected necessary inequality for *all* counted critical wall
    histories whose total cost is at most n+z. Arbitrary numbers of positive
    and zero-depth inverse steps are permitted. -/
theorem source_wall_near_cost_has_reset_bound
    (n b d m z : Nat)
    (hn : 14 ≤ n) (hz : 1 ≤ z)
    (hc : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hw : b=4*(m+n))
    (hm : m ≤ n+z) :
    3*2^z ≤ 2*(m+n+3) := by
  obtain ⟨bp,dp,mp,zp,t,k,c,s,hpre,hzEq,hbp,hbp4,hdp,hip,hkp,hcp,htp,htail⟩ :=
    counted_last_positive_reset
      (14*2^n-2*n-16) 3 b d m z hc hz
  have hodd : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
    counted_to_odd_cone _ _ _ _ _ _ hpre
  have htailProof := upper_tail_dyadic
    (2*k-4) (c+4) (mp+t+1) b d m s htail
  have htailPow : 2^s*(b+12)=(2*k-4)+12 := htailProof.1
  have htailCost : m=(mp+t+1)+s := htailProof.2
  have hprefixCost : 2*zp ≤ mp :=
    counted_cost_at_least_twice_resets _ _ _ _ _ _ hpre
  have hm1 : mp+t+1 ≤ m := by omega
  have hmz : 2*z ≤ mp+t+1 := by omega
  have hlarge : 3*2^n ≤ k+4 :=
    source_last_positive_large_left n bp dp mp t k c m z
      hn hz hodd hbp hbp4 hdp hip hkp hcp htp hm1 hmz hm
  have hwallNorm : b+12=4*(m+n+3) := by omega
  have hfirstNorm : (2*k-4)+12=2*(k+4) := by omega
  rw [hwallNorm, hfirstNorm] at htailPow
  have hscale : 2*(2^s*(2*(m+n+3))) =
      2^s*(4*(m+n+3)) := by
    calc
      2*(2^s*(2*(m+n+3))) =
        2^s*((2*2)*(m+n+3)) := by ac_rfl
      _ = 2^s*(4*(m+n+3)) := by simp
  have htailF : 2^s*(2*(m+n+3))=k+4 := by
    have h2 : 2*(2^s*(2*(m+n+3)))=2*(k+4) :=
      hscale.trans htailPow
    omega
  have hsBound : s+z ≤ n := by omega
  have hpowMono : 2^s ≤ 2^(n-z) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpowEq : 2^n = 2^(n-z)*2^z := by
    calc
      2^n = 2^((n-z)+z) := by congr 1; omega
      _ = 2^(n-z)*2^z := Nat.pow_add 2 (n-z) z
  have hpBound : 3*2^n ≤ 2^s*(2*(m+n+3)) := by omega
  have hpMul :
      2^(n-z)*(3*2^z) ≤ 2^(n-z)*(2*(m+n+3)) := by
    calc
      2^(n-z)*(3*2^z) = 3*2^n := by rw [hpowEq]; ac_rfl
      _ ≤ 2^s*(2*(m+n+3)) := hpBound
      _ ≤ 2^(n-z)*(2*(m+n+3)) :=
        Nat.mul_le_mul_right (2*(m+n+3)) hpowMono
  exact Nat.le_of_mul_le_mul_left hpMul (Nat.pow_pos (by decide))

#print axioms BB6.Agent43WallStrongGate.source_wall_near_cost_has_reset_bound

end BB6.Agent43WallStrongGate
