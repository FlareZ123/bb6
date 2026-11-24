import SingularTerminal
namespace SheepWeightedResidual

theorem type3_ratio_mod (H B k m i r : Nat)
    (hm : 1<m) (h1683 : 1683%m=0)
    (hi : (i*2)%m=1) (hr : (i*3)%m=r)
    (heq : 3^H*(19+1683*k)=2^H*(2^B-1)) :
    2^B%m=(1+19*r^H)%m := by
  have hM : (3^H*1683)%m=0 := by rw [Nat.mul_mod, h1683, Nat.mul_zero, Nat.zero_mod]
  have hI : (i^H*2^H)%m=1 := by rw [←Nat.mul_pow, Nat.pow_mod,hi,Nat.one_pow,Nat.mod_eq_of_lt hm]
  have h := linear_mod_inverse (2^H) (3^H*19+2^H) (3^H*1683) (2^B) k m (i^H)
    (terminal_linear (3^H) (2^H) 19 1683 (2^B) k (Nat.one_le_pow B 2 (by decide)) heq) hM hI
  calc
    2^B%m = (i^H*(3^H*19+2^H))%m := h
    _ = (19*(i*3)^H+i^H*2^H)%m := by rw [Nat.mul_add,Nat.mul_pow]; ac_rfl
    _ = ((19*(i*3)^H)%m+1)%m := by rw [Nat.add_mod, hI]
    _ = (1+19*r^H)%m := by
      have hh : (19*(i*3)^H)%m=(19*r^H)%m := by
        rw [Nat.mul_mod 19, Nat.pow_mod (i*3), hr, ←Nat.mul_mod 19]
      rw [hh, Nat.add_comm]
      symm
      rw [Nat.add_mod 1]
      simp [Nat.mod_eq_of_lt hm]

theorem ratio_period_reduce (a m p n : Nat) (hc : a^p%m=1) :
    (1+19*a^n)%m=(1+19*a^(n%p))%m := by
  rw [Nat.add_mod 1, Nat.mul_mod 19, base_period_reduce a m p n hc, ←Nat.mul_mod 19, ←Nat.add_mod]

private theorem type3_p11_finite : ∀ h : Fin 10, ∀ b : Fin 10, b.val%2=0 →
    2^b.val%11=(1+19*7^h.val)%11 →
    h.val=0 ∨ h.val=4 ∨ h.val=5 ∨ h.val=7 := by decide
private theorem type3_p17_finite : ∀ h : Fin 16, ∀ b : Fin 8, b.val%2=0 →
    2^b.val%17=(1+19*10^h.val)%17 →
    h.val=1 ∨ h.val=5 ∨ h.val=8 := by decide

theorem type3_terminal_hidden_classes (k H B : Nat) (hH : 1≤H)
    (heq : 3^H*(19+1683*k)=2^H*(2^B-1)) :
    H%80=5 ∨ H%80=17 ∨ H%80=24 ∨ H%80=37 ∨ H%80=40 ∨ H%80=65 := by
  have hd : 3^H ∣ 2^H*(2^B-1) := ⟨19+1683*k,heq.symm⟩
  have hc : (3^H).Coprime (2^H) := Nat.Coprime.pow H H (by decide)
  have hdiv := three_power_dvd_two_pow_sub_one H B hH (hc.dvd_of_dvd_mul_left hd)
  have hb : B%2=0 := Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_trans (Nat.dvd_mul_right 2 (3^(H-1))) hdiv)
  have h11 := type3_ratio_mod H B k 11 6 7 (by decide) (by decide) (by decide) (by decide) heq
  have h17 := type3_ratio_mod H B k 17 9 10 (by decide) (by decide) (by decide) (by decide) heq
  rw [base_period_reduce 2 11 10 B (by decide),ratio_period_reduce 7 11 10 H (by decide)] at h11
  rw [base_period_reduce 2 17 8 B (by decide),ratio_period_reduce 10 17 16 H (by decide)] at h17
  have hr11 := type3_p11_finite ⟨H%10, Nat.mod_lt _ (by decide)⟩ ⟨B%10,Nat.mod_lt _ (by decide)⟩ (by simp; omega) h11
  have hr17 := type3_p17_finite ⟨H%16, Nat.mod_lt _ (by decide)⟩ ⟨B%8,Nat.mod_lt _ (by decide)⟩ (by simp; omega) h17
  simp at hr11 hr17
  omega

#print axioms type3_terminal_hidden_classes
end SheepWeightedResidual
