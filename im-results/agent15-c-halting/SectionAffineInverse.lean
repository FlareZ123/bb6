import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- Every even high output whose counter sum is 1 mod 4 has one
    and only one source, in the direct affine branch. -/
theorem section_sum_one_even_iff_affine (a k x y : Nat)
    (hy : 4≤y) (heven : y%2=0) (hs : (x+y)%4=1) :
    secNext (a,k)=some (x,y) ↔
      a=x+y-2 ∧ k=(y-2)/2 := by
  constructor
  · intro h
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,hk0] at h
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,hk0,hk1] at h
          omega
        · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
          have hh := BB6.Agent3.bounce_large_image _ _ _ _ hb hy
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
                  simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
                have hh := BB6.Agent3.bounce_large_image _ _ _ _ hb hy
                omega
      · by_cases hk0 : k=0
        · simp [secNext,exactSection,ha0,ha1,hk0] at h
          omega
        · by_cases hregion : 2*k≤a
          · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
            omega
          · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
              simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
            have hh := BB6.Agent3.bounce_large_image _ _ _ _ hb hy
            omega
  · rintro ⟨rfl,rfl⟩
    have ha0 : x+y-2≠0 := by omega
    have ha1 : x+y-2≠1 := by omega
    have hk0 : (y-2)/2≠0 := by omega
    have hreg : 2*((y-2)/2)≤x+y-2 := by omega
    simp [secNext,exactSection,ha0,ha1,hk0,hreg]
    omega

#print axioms section_sum_one_even_iff_affine
end BB6.Agent15
