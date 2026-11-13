import QDepthSelector
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000

namespace CascadeQDepthHensel
open CascadeRayDepthHensel CascadeRayDepthResidue CascadeRayPeriod

/-- Exact n=887 selector values through precision eight. -/
theorem qDepthResidue_887_table :
    qDepthResidue 887 0=0 ∧ qDepthResidue 887 1=0 ∧
    qDepthResidue 887 2=0 ∧ qDepthResidue 887 3=0 ∧
    qDepthResidue 887 4=0 ∧ qDepthResidue 887 5=0 ∧
    qDepthResidue 887 6=486 ∧ qDepthResidue 887 7=3402 := by
  have h0 : (3:Int)^6∣qNumerator 887 0 := by decide
  have h486 : (3:Int)^7∣qNumerator 887 486 := by decide
  have h3402 : (3:Int)^8∣qNumerator 887 3402 := by decide
  have hzero : ∀ k≤5, qDepthResidue 887 k=0 := by
    intro k hk
    have hpow : (3:Int)^6=(3:Int)^(k+1)*(3:Int)^(5-k) := by
      rw [←Int.pow_add]
      congr 1
      omega
    have hdiv : (3:Int)^(k+1)∣(3:Int)^6 := by
      rw [hpow]
      exact Int.dvd_mul_right _ _
    have hlow : (3:Int)^(k+1)∣qNumerator 887 0 :=
      Int.dvd_trans hdiv h0
    have hsel := (qDepthResidue_iff 887 k 0 (by omega)).mp hlow
    simpa using hsel.symm
  have h6sel := (qDepthResidue_iff 887 6 486 (by omega)).mp h486
  have h7sel := (qDepthResidue_iff 887 7 3402 (by omega)).mp h3402
  have hp6 : depthPeriod 6=1458 := by decide
  have hp7 : depthPeriod 7=4374 := by decide
  have h6 : qDepthResidue 887 6=486 := by
    rw [hp6] at h6sel
    rw [Nat.mod_eq_of_lt (by decide : 486<1458)] at h6sel
    exact h6sel.symm
  have h7 : qDepthResidue 887 7=3402 := by
    rw [hp7] at h7sel
    rw [Nat.mod_eq_of_lt (by decide : 3402<4374)] at h7sel
    exact h7sel.symm
  exact ⟨hzero 0 (by omega),hzero 1 (by omega),hzero 2 (by omega),
    hzero 3 (by omega),hzero 4 (by omega),hzero 5 (by omega),h6,h7⟩

#print axioms qDepthResidue_iff
#print axioms qDepthResidue_unique_in_period
#print axioms qDepthResidue_887_table

#print axioms qDepthResidue_iff
#print axioms qDepthResidue_unique_in_period
#print axioms qDepthResidue_887_table
end CascadeQDepthHensel
