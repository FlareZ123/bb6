import Lean
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3ValSix

/-- Every source-authentic high stopping gate in this arithmetic
index family lands in the four-link forbidden original-blank cylinder. -/
theorem second_cone_high_arithmetic (j m k:Nat)
    (hm:4≤m) (hj:j%128=81) (hpair:(j+63)%256=(3*m)%256)
    (hstop:k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%256=165 ∧ k%256=26 := by
  have hdiv : 256 ∣ 2^(2*m+2) := by
    change 2^8 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨q,hq⟩ := hdiv
  have hfactor : k+j+3*m+5=256*(q*(j+3)) := by
    calc
      k+j+3*m+5=2^(2*m+2)*(j+3) := hstop
      _=(256*q)*(j+3) := by rw [hq]
      _=256*(q*(j+3)) := by ac_rfl
  have hdiv256 : (k+j+3*m+5)%256=0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact ⟨q*(j+3),hfactor⟩
  omega

#print axioms second_cone_high_arithmetic
end BB6.Agent3ValSix
