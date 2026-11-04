import GeneralMod8Inverse
import FastSectionDef
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Fully general unique-predecessor restriction for the exact Machine C
    section's odd-odd output sector with x+y=4 mod8. All source branches
    and all recursive bounce depths are covered. -/
theorem section_oddodd_sum4_inverse (a k x y : Nat)
    (hy : 5≤y) (hyodd : y%2=1) (hmod : (x+y)%8=4)
    (h : secNext (a,k)=some (x,y)) :
    a=(x+y-4)/2 ∧ k=(x+3*y-10)/4 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
        omega
      · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        have ht := odd_bounce_mod8_forces_terminal (2*k+1) 1 x y hb
          (by decide) hmod
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
          omega
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
            omega
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · have hb : (bounce 4 (2*k-3)).2=some (x,y) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              obtain ⟨n,hsum,_⟩ :=
                bounce_even_output_invariants (2*k-3) 4 x y
                  (by decide) (by omega) hb
              have heven : x+y+1=2*(2^n*8) := by
                calc
                  x+y+1=2^n*(2*4+8) := hsum
                  _ = 2^n*16 := by rfl
                  _ = 2*(2^n*8) := by ac_rfl
              omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hregion] using h
          by_cases he : a%2=0
          · have hodd : (a-1)%2=1 := by omega
            obtain ⟨hsum,hcounter⟩ :=
              odd_bounce_mod8_forces_terminal (2*k-a+3) (a-1)
                x y hb hodd hmod
            constructor <;> omega
          · have hodd : (a-1)%2=0 := by omega
            obtain ⟨n,hsum,_⟩ :=
              bounce_even_output_invariants (2*k-a+3) (a-1)
                x y hodd (by omega) hb
            have hfactor : 2*(a-1)+8=2*(a+3) := by omega
            have heven : x+y+1=2*(2^n*(a+3)) := by
              calc
                x+y+1=2^n*(2*(a-1)+8) := hsum
                _ = 2^n*(2*(a+3)) := by rw [hfactor]
                _ = 2*(2^n*(a+3)) := by ac_rfl
            omega

#print axioms section_oddodd_sum4_inverse

end BB6.Agent46
