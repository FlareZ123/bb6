import SectionAllInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20C70
open BB6.Agent46

/-- Exact predecessor fibre for even-right outputs with sum 7 mod 16.
    All original-section source cases, including the exceptional small ones,
    are retained by the imported complete inverse grammar. -/
theorem seven_inverse (a k x y : Nat)
    (hy : 6 ≤ y) (he : y % 2 = 0) (hs : (x+y)%16 = 7)
    (hedge : secNext (a,k) = some (x,y)) :
    (a=x+y-2 ∧ y=2*k+2) ∨
    (x+y=4*a+11 ∧ x+2*y=2*k+a+10) := by
  have hsource := (section_preimage_all_iff a k x y).mp hedge
  have hOdd : (x+y)%2 = 1 := by omega
  have hEight : (x+y+1)%16=8 := by omega
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll, ha0, hk0] at hsource
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll, ha0, hk0, hk1] at hsource
        omega
      · simp only [sectionPreimageAll, if_pos ha0, if_neg hk0, if_neg hk1] at hsource
        obtain ⟨_, n, hsum, _⟩ := hsource
        have h8div : 8 ∣ x+y := by
          refine ⟨2^n,?_⟩
          omega
        have hzero := Nat.mod_eq_zero_of_dvd h8div
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hsource
        omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hsource
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hsource
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hsource
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hsource
              rcases hsource with hsmall | ⟨_,n,hsum,_⟩
              · omega
              · have h16div : 16 ∣ x+y+1 := by
                  refine ⟨2^n,?_⟩
                  omega
                have hzero := Nat.mod_eq_zero_of_dvd h16div
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hsource
        omega
      · by_cases hregion : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
            if_neg hk0,if_pos hregion] at hsource
          rcases hsource with ⟨hx,hy'⟩
          left
          omega
        · by_cases haEven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hregion,if_pos haEven] at hsource
            obtain ⟨_,n,hsum,_⟩ := hsource
            have hfactor : 2*(a-1)+6=2*(a+2) := by omega
            have hEvenSum : 2 ∣ x+y := by
              refine ⟨2^n*(a+2),?_⟩
              rw [hsum,hfactor]
              ac_rfl
            have hzero := Nat.mod_eq_zero_of_dvd hEvenSum
            omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hregion,if_neg haEven] at hsource
            rcases hsource with hsmall | hlarge
            · omega
            obtain ⟨_,n,hsum,hcost⟩ := hlarge
            have haOdd : a%2=1 := by omega
            have hfactor : 2*(a-1)+8=4*(a/2+2) := by omega
            have hnle : n ≤ 1 := by
              by_cases hn : n ≤ 1
              · exact hn
              have hn2 : 2≤n := by omega
              have h4 : 4 ∣ 2^n := by
                have hh : (2:Nat)^2 ∣ (2:Nat)^n := Nat.pow_dvd_pow 2 hn2
                simpa using hh
              obtain ⟨w,hw⟩ := h4
              have h16div : 16 ∣ x+y+1 := by
                refine ⟨w*(a/2+2),?_⟩
                calc
                  x+y+1 = 2^n*(2*(a-1)+8) := hsum
                  _ = (4*w)*(4*(a/2+2)) := by rw [hw,hfactor]
                  _ = (4*4)*(w*(a/2+2)) := by ac_rfl
                  _ = 16*(w*(a/2+2)) := by rfl
              have hzero := Nat.mod_eq_zero_of_dvd h16div
              omega
            have hnCases : n=0 ∨ n=1 := by omega
            rcases hnCases with hzero | hone
            · rw [hzero] at hsum hcost
              simp at hsum hcost
              omega
            · rw [hone] at hsum hcost
              simp at hsum hcost
              right
              omega

#print axioms seven_inverse
end BB6.Agent20C70
