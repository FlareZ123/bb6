import PositiveMassOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- The exact mass-plus-four transitions are precisely the direct positive
    right-counter branches. -/
theorem section_delta_four_iff_direct (a k x y : Nat)
    (h : secNext (a,k)=some (x,y)) :
    x+2*y=a+2*k+4 ↔ 2≤a ∧ 0<k ∧ 2*k≤a := by
  constructor
  · intro he
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,hk0] at h
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,hk0,hk1] at h
          omega
        · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
          have hh := bounce_odd_mass_lower 1 (2*k+1) x y (by decide) hb
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
                have hh := bounce_even_mass_lower 4 (2*k-3) x y (by decide) hb
                omega
      · by_cases hk0 : k=0
        · simp [secNext,exactSection,ha0,ha1,hk0] at h
          omega
        · by_cases hl : 2*k≤a
          · omega
          · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
              simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hl] using h
            by_cases ev : a%2=0
            · have hh := bounce_odd_mass_lower (a-1) (2*k-a+3) x y (by omega) hb
              omega
            · have hh := bounce_even_mass_lower (a-1) (2*k-a+3) x y (by omega) hb
              omega
  · rintro ⟨ha,hk,hl⟩
    have hh:=h
    simp [secNext,exactSection,show a≠0 by omega,
      show a≠1 by omega,show k≠0 by omega,hl] at hh
    omega

#print axioms section_delta_four_iff_direct
end BB6.Agent46
