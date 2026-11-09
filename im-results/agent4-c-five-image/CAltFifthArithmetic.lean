import SectionAllInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Five
open BB6.Agent46

private theorem odd_pow_factor (a n w t : Nat)
    (haodd : a%2=1)
    (hp : 64*w+25+64*t+14+1=(2:Nat)^n*(2*(a-1)+8)) : n≤1 := by
  by_cases hn : n≤1
  · exact hn
  have hn2 : 2≤n := by omega
  have hpow : (2:Nat)^2 ∣ (2:Nat)^n := Nat.pow_dvd_pow 2 hn2
  have hfac : 4 ∣ 2*(a-1)+8 := by
    refine ⟨(a-1)/2+2,?_⟩
    omega
  obtain ⟨v,hv⟩ := hpow
  obtain ⟨z,hz⟩ := hfac
  have hdiv : 16 ∣ 64*w+25+64*t+14+1 := by
    refine ⟨v*z,?_⟩
    calc
      64*w+25+64*t+14+1 = (2:Nat)^n*(2*(a-1)+8) := hp
      _ = (4*v)*(4*z) := by rw [←hv,←hz]
      _ = 16*(v*z) := by simp only [show (16:Nat)=4*4 by decide]; ac_rfl
  have hmod : (64*w+25+64*t+14+1)%16=0 := Nat.mod_eq_zero_of_dvd hdiv
  omega

private theorem even_sum_no_even_power (a n w t : Nat)
    (hp : 64*w+25+64*t+14=(2:Nat)^n*(2*(a-1)+6)) : False := by
  have hdiv : 2 ∣ 64*w+25+64*t+14 := by
    refine ⟨(2:Nat)^n*((a-1)+3),?_⟩
    calc
      64*w+25+64*t+14=(2:Nat)^n*(2*(a-1)+6) := hp
      _=(2:Nat)^n*(2*((a-1)+3)) := by congr 1
      _=2*((2:Nat)^n*((a-1)+3)) := by ac_rfl
  have hmod : (64*w+25+64*t+14)%2=0 := Nat.mod_eq_zero_of_dvd hdiv
  omega

/-- All original-source preimages of this residue cylinder are among two explicit states. -/
theorem two_parent_arithmetic (a k w t : Nat)
    (h : sectionPreimageAll a k (64*w+25) (64*t+14)) :
    (a=64*(w+t)+37 ∧ k=32*t+6) ∨
    (a=16*(w+t)+7 ∧ k=24*w+56*t+18) := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at h
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at h
        obtain ⟨_,n,hs,_⟩ := h
        have hdiv : 2 ∣ 64*w+25+64*t+14 := by
          refine ⟨(2:Nat)^n*4,?_⟩
          calc
            64*w+25+64*t+14 = (2:Nat)^n*8 := hs
            _ = 2*((2:Nat)^n*4) := by omega
        have hmod : (64*w+25+64*t+14)%2=0 := Nat.mod_eq_zero_of_dvd hdiv
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at h
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              rcases h with h3 | ⟨_,n,hs,_⟩
              · omega
              · have hdiv : 16 ∣ 64*w+25+64*t+14+1 := by
                  refine ⟨(2:Nat)^n,?_⟩
                  calc
                    64*w+25+64*t+14+1=(2:Nat)^n*16 := hs
                    _=16*(2:Nat)^n := by omega
                have hmod : (64*w+25+64*t+14+1)%16=0 := Nat.mod_eq_zero_of_dvd hdiv
                omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
            if_neg hk0,if_pos hlow] at h
          left
          omega
        · by_cases haeven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos haeven] at h
            obtain ⟨_,n,hs,_⟩ := h
            exact False.elim (even_sum_no_even_power a n w t hs)
          · have haodd : a%2=1 := by omega
            simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at h
            rcases h with ⟨hy,_⟩ | ⟨_,n,hs,hc⟩
            · omega
            · have hn := odd_pow_factor a n w t haodd hs
              by_cases hz : n=0
              · subst n
                simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_zero,
                  Nat.add_zero] at hs hc
                omega
              · have hn1 : n=1 := by omega
                subst n
                simp only [Nat.pow_one] at hs hc
                right
                omega

#print axioms odd_pow_factor
#print axioms two_parent_arithmetic
end BB6.Agent4Five
