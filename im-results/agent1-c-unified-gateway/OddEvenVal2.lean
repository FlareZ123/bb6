import SectionAllInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent1Unified
open BB6.Agent46

/-- All odd-first, even-right source outputs with x+y+1 exactly
    4 modulo 8 have one and only one direct predecessor. -/
theorem odd_even_val2_forces_direct (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=0) (hy4 : 4≤y)
    (hm : (x+y+1)%8=4)
    (he : secNext (a,k)=some (x,y)) :
    a=x+y-2 ∧ 2*k+2=y := by
  have hi := (section_preimage_all_iff a k x y).mp he
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hi
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hi
        omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at hi
        obtain ⟨_,n,hs,_⟩ := hi
        have hev : 2 ∣ 2^n*8 := ⟨2^n*4,by omega⟩
        have hmod : (x+y)%2=0 := by
          rw [hs]
          exact Nat.mod_eq_zero_of_dvd hev
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hi
        omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hi
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hi
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hi
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hi
              rcases hi with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hd : 8 ∣ 2^n*16 := ⟨2^n*2,by omega⟩
                have hm0 : (x+y+1)%8=0 := by
                  rw [hpow]
                  exact Nat.mod_eq_zero_of_dvd hd
                omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hi
        omega
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
            if_neg hk0,if_pos hlow] at hi
          rcases hi with ⟨hxx,hyy⟩
          omega
        · by_cases haEven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos haEven] at hi
            obtain ⟨_,n,hpow,_⟩ := hi
            have hdiv : 2 ∣ 2^n*(2*(a-1)+6) := by
              refine ⟨2^n*((a-1)+3),?_⟩
              calc
                2^n*(2*(a-1)+6) = 2^n*(2*((a-1)+3)) := by
                  congr 1 <;> omega
                _ = 2*(2^n*((a-1)+3)) := by ac_rfl
            have hmod : (x+y)%2=0 := by
              rw [hpow]
              exact Nat.mod_eq_zero_of_dvd hdiv
            omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haEven] at hi
            rcases hi with ⟨hy3,_⟩ | ⟨_,n,hpow,hcost⟩
            · omega
            · have haOdd : a%2=1 := by omega
              cases n with
              | zero =>
                  simp at hpow hcost
                  omega
              | succ n =>
                  have hb : 4 ∣ 2*(a-1)+8 := by
                    refine ⟨(a-1)/2+2,?_⟩
                    omega
                  obtain ⟨b,hb⟩ := hb
                  have h8 : 8 ∣ 2^(n+1)*(2*(a-1)+8) := by
                    refine ⟨2^n*b,?_⟩
                    calc
                      2^(n+1)*(2*(a-1)+8) = (2^n*2)*(4*b) := by
                        rw [Nat.pow_succ,hb]
                      _ = 8*(2^n*b) := by
                        have hprod : (8:Nat)=2*4 := by decide
                        rw [hprod]
                        ac_rfl
                  have hz : (x+y+1)%8=0 := by
                    rw [hpow]
                    exact Nat.mod_eq_zero_of_dvd h8
                  omega

#print axioms odd_even_val2_forces_direct
end BB6.Agent1Unified
