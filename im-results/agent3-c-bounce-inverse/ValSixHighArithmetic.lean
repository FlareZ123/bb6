import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix

private theorem power_dominates_linear (m : Nat) :
    3*m+2 ≤ 2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2=(2*m+2)+2 := by omega
      rw [he,Nat.pow_add]
      have hf : (2:Nat)^2=4 := by decide
      rw [hf]
      have hp : 0<2^(2*m+2) := Nat.pow_pos (by decide)
      omega

/-- For all unbounded m,j satisfying the authentic high stopping
equation, a new arithmetic family lands in the valuation-six cylinder. -/
theorem high_val_six_arithmetic (j m k : Nat)
    (hm : 4≤m) (hm8 : m%8=4)
    (hpair : (j+191)%256=(3*m)%256)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%16=13 ∧ k%16=2 ∧ 34≤k ∧
    ((2*j+3)+k+1)%256=64 ∧ 320≤(2*j+3)+k+1 := by
  have hdiv : 256 ∣ 2^(2*m+2) := by
    change 2^8 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨q,hq⟩ := hdiv
  have hfactor : k+j+3*m+5=256*(q*(j+3)) := by
    calc
      k+j+3*m+5 = 2^(2*m+2)*(j+3) := hstop
      _=(256*q)*(j+3) := by rw [hq]
      _=256*(q*(j+3)) := by ac_rfl
  have hdiv256 : (k+j+3*m+5)%256=0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact ⟨q*(j+3),hfactor⟩
  have hpowpos : 0<2^(2*m+2) := Nat.pow_pos (by decide)
  have hpower : 1024≤2^(2*m+2) := by
    have hh : (2:Nat)^10≤2^(2*m+2) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    simpa only [show (2:Nat)^10=1024 by decide] using hh
  have hgrow := power_dominates_linear m
  have hj : j ≤ 2^(2*m+2)*j := by
    have hp : 1≤2^(2*m+2) := by omega
    simpa using (Nat.mul_le_mul_right j hp)
  have hbig : 3*m+325 ≤ 3*2^(2*m+2) := by omega
  have hbound : 320≤k := by
    rw [Nat.mul_add] at hstop
    omega
  have hmods : (2*j+3)%16=13 ∧ k%16=2 ∧
      ((2*j+3)+k+1)%256=64 := by omega
  refine ⟨hmods.1,hmods.2.1,(by omega),hmods.2.2,?_⟩
  omega

#print axioms high_val_six_arithmetic
end BB6.Agent3ValSix
