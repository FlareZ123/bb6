import SectionMassStrict
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Every positive-right successful section adds at least four to weighted
    mass. The only possible delta-two branches have right counter zero. -/
theorem section_mass_four_if_right_positive (a k x y : Nat)
    (hk : 0 < k) (h : secNext (a,k)=some (x,y)) :
    a+2*k+4≤x+2*y := by
  by_cases ha0 : a=0
  · by_cases hk1 : k=1
    · simp [secNext,exactSection,ha0,hk1] at h
      omega
    · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
        have hk0 : k≠0 := by omega
        simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
      have hh := bounce_odd_mass_lower 1 (2*k+1) x y (by decide) hb
      omega
  · by_cases ha1 : a=1
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,ha1,hk1] at h
        omega
      · by_cases hk2 : k=2
        · simp [secNext,exactSection,ha0,ha1,hk1,hk2] at h
          omega
        · by_cases hk3 : k=3
          · simp [secNext,exactSection,ha0,ha1,hk1,hk2,hk3] at h
            omega
          · have hk0 : k≠0 := by omega
            have hb : (bounce 4 (2*k-3)).2=some (x,y) := by
              simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
            have hh := bounce_even_mass_lower 4 (2*k-3) x y (by decide) hb
            omega
    · have hk0 : k≠0 := by omega
      by_cases hlow : 2*k≤a
      · simp [secNext,exactSection,ha0,ha1,hk0,hlow] at h
        omega
      · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow] using h
        by_cases he : a%2=0
        · have hh := bounce_odd_mass_lower (a-1) (2*k-a+3) x y (by omega) hb
          omega
        · have hh := bounce_even_mass_lower (a-1) (2*k-a+3) x y (by omega) hb
          omega

/-- The exact and only successful mass-plus-two transitions. -/
theorem section_delta_two_iff_right_zero (a k x y : Nat)
    (h : secNext (a,k)=some (x,y)) :
    x+2*y = a+2*k+2 ↔ 2≤a ∧ k=0 := by
  constructor
  · intro he
    by_cases hk : k=0
    · by_cases ha0 : a=0
      · simp [secNext,exactSection,hk,ha0] at h
      · by_cases ha1 : a=1
        · simp [secNext,exactSection,hk,ha0,ha1] at h
          omega
        · omega
    · have hh := section_mass_four_if_right_positive a k x y (by omega) h
      omega
  · rintro ⟨ha,hk⟩
    have hh:=h
    simp [secNext,exactSection,hk,show a≠0 by omega,show a≠1 by omega] at hh
    omega

#print axioms section_mass_four_if_right_positive
#print axioms section_delta_two_iff_right_zero
end BB6.Agent46
