import Low124Rectangle
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3

private theorem high_124_margin (m : Nat) (hm : 3≤m) :
    3*m+261 ≤ 3*(2:Nat)^(2*m+2) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hsmall : m<3
      · have htwo : m=2 := by omega
        subst m
        decide
      · have hprev := ih (by omega)
        have hp : (2:Nat)^(2*(m+1)+2) = 4*2^(2*m+2) := by
          rw [show 2*(m+1)+2=(2*m+2)+2 by omega, Nat.pow_add]
          simp only [show (2:Nat)^2=4 by decide]
          omega
        rw [hp]
        have hpos : 0 < (2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
        omega

/-- The original higher stopping family at j = 31 mod 32 and
j+3m = 127 mod 128, m at least 3, misses the entire true blank
orbit. Every index satisfying the hypotheses is covered. -/
theorem blank_no_high_124 (j m k : Nat)
    (hj : j%32=31) (hm : 3≤m)
    (hmod : (j+3*m)%128=127)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) : ¬ CReach (2*j+3) k := by
  have hdiv : 128 ∣ (2:Nat)^(2*m+2) := by
    change 2^7 ∣ (2:Nat)^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hdiv2 : 128 ∣ 2^(2*m+2)*(j+3) := by
    rcases hdiv with ⟨t,ht⟩
    refine ⟨t*(j+3),?_⟩
    rw [ht]
    simp only [Nat.mul_assoc]
  have hr : (k+j+3*m+5)%128=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hdiv2
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hjlow : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  have hmlow := high_124_margin m hm
  have hlarge : 256≤k := by
    rw [Nat.mul_add] at hstop
    omega
  have hrectx : (2*j+3)%64=1 := by omega
  have hrecty : k%128=124 := by omega
  exact blank_no_rectangle_1_124 (2*j+3) k hrectx hrecty hlarge

#print axioms blank_no_high_124
end BB6.Agent3
