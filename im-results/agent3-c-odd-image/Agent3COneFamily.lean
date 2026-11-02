import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Every target on the entire infinite line (1,4*j), j positive,
    has a unique exact source section predecessor (4*j-1,2*j-1). -/
theorem section_one_four_exact (a k j : Nat) (hj : 1≤j) :
    secNext (a,k)=some (1,4*j) ↔ a=4*j-1 ∧ k=2*j-1 := by
  constructor
  · intro h
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,hk0] at h
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,hk0,hk1] at h
        · have hb : (bounce 1 (2*k+1)).2=some (1,4*j) := by
            simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
          have hh := bounce_large_image _ _ _ _ hb (by omega)
          omega
    · by_cases ha1 : a=1
      · by_cases hk0 : k=0
        · simp [secNext,exactSection,ha0,ha1,hk0] at h
        · by_cases hk1 : k=1
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
          · by_cases hk2 : k=2
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
            · by_cases hk3 : k=3
              · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
              · have hb : (bounce 4 (2*k-3)).2=some (1,4*j) := by
                  simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
                have hh := bounce_large_image _ _ _ _ hb (by omega)
                omega
      · by_cases hk0 : k=0
        · simp [secNext,exactSection,ha0,ha1,hk0] at h
          omega
        · by_cases hregion : 2*k≤a
          · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
            omega
          · have hb : (bounce (a-1) (2*k-a+3)).2=some (1,4*j) := by
              simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
            have hh := bounce_large_image _ _ _ _ hb (by omega)
            omega
  · rintro ⟨rfl,rfl⟩
    have hpre : 2*(2*j-1)≤4*j-1 := by omega
    have ha0 : 4*j-1≠0 := by omega
    have ha1 : 4*j-1≠1 := by omega
    have hk0 : 2*j-1≠0 := by omega
    simp [secNext,exactSection,ha0,ha1,hk0,hpre]
    omega

#print axioms section_one_four_exact
end BB6.Agent3
