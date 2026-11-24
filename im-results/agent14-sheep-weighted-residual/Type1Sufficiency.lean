import TerminalSufficiency
namespace SheepWeightedResidual

def type1Q (H : Nat) : Nat := 2*(5*2^(18-((H+5)%18))%27)

private theorem type1_q_small : ∀ h : Fin 18,
    0<type1Q h.val ∧ (type1Q h.val)%2=0 ∧
    (16*2^h.val*type1Q h.val)%27=5 := by decide

theorem type1_q_conditions (H : Nat) :
    0<type1Q H ∧ (type1Q H)%2=0 ∧ (16*2^H*type1Q H)%27=5 := by
  have hq : type1Q (H%18)=type1Q H := by
    unfold type1Q
    have h : ((H%18)+5)%18=(H+5)%18 := by omega
    rw [h]
  have ht := type1_q_small ⟨H%18,Nat.mod_lt H (by decide)⟩
  simp only at ht
  rw [hq] at ht
  obtain ⟨hp,he,hm⟩ := ht
  refine ⟨hp,he,?_⟩
  rw [Nat.mul_mod (16*2^H),Nat.mul_mod 16,base_period_reduce 2 27 18 H (by decide)]
  rw [Nat.mul_mod (16*2^(H%18)),Nat.mul_mod 16] at hm
  exact hm

private theorem four_dvd_even_multiplier (u q : Nat) (he : q%2=0) : (2*u*q)%4=0 := by
  obtain ⟨v,hv⟩ := Nat.dvd_iff_mod_eq_zero.mpr he
  rw [hv]
  have h : 2*u*(2*v)=4*(u*v) := by grind
  rw [h]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right 4 (u*v))

private theorem crt135 (y : Nat) (h27 : y%27=5) (h5 : y%5=0) : y%135=5 := by omega

theorem type1_terminal_exists_high (H : Nat) (hH : 3≤H) :
    ∃ k B : Nat, 1≤k ∧ 1≤B ∧ 3^H*(5+135*k)=2^H*(2^B-1) := by
  let q := type1Q H
  obtain ⟨hq,hqe,h27⟩ := type1_q_conditions H
  obtain ⟨z,hz⟩ := type1_exponent_lift H q hH
  let B := 2*3^(H-1)*q
  let v := 16*q+27*z
  let y := 2^H*v
  have hy27 : y%27=5 := by
    dsimp [y,v]
    have h : 2^H*(16*q+27*z)=16*2^H*q+27*(2^H*z) := by grind
    rw [h,Nat.add_mod,Nat.mul_mod 27]; simpa [q] using h27
  have hB4 : B%4=0 := four_dvd_even_multiplier (3^(H-1)) q hqe
  have hpow5 : 2^B%5=1 := by rw [base_period_reduce 2 5 4 B (by decide),hB4]
  have hv5 : (3^H*v)%5=0 := by
    change 2^B=1+3^H*v at hz
    rw [hz] at hpow5
    exact add_mod_cancel 5 1 (3^H*v) 0 hpow5
  have hi : (2^H*3^H)%5=1 := by
    rw [←Nat.mul_pow,Nat.pow_mod]
    simp
  have hV5 : v%5=0 := by
    have hh : (3^H*v)%5=(3^H*0)%5 := by simpa using hv5
    exact mul_mod_cancel 5 (3^H) (2^H) v 0 hi hh
  have hy5 : y%5=0 := by dsimp [y]; rw [Nat.mul_mod,hV5]; simp
  have hy : y%135=5 := crt135 y hy27 hy5
  have hylo : 5<y := by
    have hpow : 8≤2^H := Nat.pow_le_pow_right (by decide : 0<2) hH
    have hv : 1≤v := by
      change 1≤16*q+27*z
      have hp : 0<q := hq
      omega
    have hp := Nat.mul_le_mul_left (2^H) hv
    simp at hp
    exact Nat.lt_of_lt_of_le (by decide : 5<8) (Nat.le_trans hpow hp)
  let k := y/135
  have hyform : y=5+135*k := by
    have hh:=Nat.mod_add_div y 135
    rw [hy] at hh
    exact hh.symm
  have hk : 1≤k := by rw [hyform] at hylo; omega
  have hB : 1≤B := Nat.mul_pos (Nat.mul_pos (by decide : 0<2) (Nat.pow_pos (by decide))) hq
  refine ⟨k,B,hk,hB,?_⟩
  rw [←hyform,hz]
  change 3^H*(2^H*v)=2^H*((1+3^H*v)-1)
  rw [Nat.add_comm 1,Nat.add_sub_cancel]
  ac_rfl

set_option exponentiation.threshold 400 in
theorem type1_hidden_iff (H : Nat) :
    (∃ k B : Nat, 1≤k ∧ 1≤B ∧ 3^H*(5+135*k)=2^H*(2^B-1)) ↔ 1≤H := by
  constructor
  · rintro ⟨k,B,hk,hB,he⟩
    by_cases hz : H=0
    · subst H
      exact False.elim (type1_H0 k B he)
    · omega
  · intro hH
    by_cases hh : 3≤H
    · exact type1_terminal_exists_high H hh
    · have he : H=1 ∨ H=2 := by omega
      rcases he with rfl|rfl
      · exact ⟨21209715,32,by decide,by decide,by decide⟩
      · exact ⟨(4*(2^300-1)/9-5)/135,300,by decide,by decide,by decide⟩

#print axioms type1_hidden_iff
end SheepWeightedResidual
