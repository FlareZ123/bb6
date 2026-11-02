import Agent3CImage
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- Exact unique source of the entire two-dimensional section target family
    (a ≡ 1 mod 4, k ≡ 0 mod 8, k positive). -/
theorem section_one_eight_exact (a k u v : Nat) :
    secNext (a,k)=some (4*u+1,8*(v+1)) ↔
    a=4*u+8*(v+1)-1 ∧ k=4*(v+1)-1 := by
  constructor
  · intro h
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,hk0] at h
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,hk0,hk1] at h
        · have hb : (bounce 1 (2*k+1)).2=some (4*u+1,8*(v+1)) := by
            simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
          have hh := BB6.Agent3.bounce_large_image _ _ _ _ hb (by omega)
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
              · have hb : (bounce 4 (2*k-3)).2=some (4*u+1,8*(v+1)) := by
                  simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
                have hh := BB6.Agent3.bounce_large_image _ _ _ _ hb (by omega)
                omega
      · by_cases hk0 : k=0
        · simp [secNext,exactSection,ha0,ha1,hk0] at h
          omega
        · by_cases hregion : 2*k≤a
          · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
            omega
          · have hb : (bounce (a-1) (2*k-a+3)).2=some (4*u+1,8*(v+1)) := by
              simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
            have hh := BB6.Agent3.bounce_large_image _ _ _ _ hb (by omega)
            omega
  · rintro ⟨rfl,rfl⟩
    have hpre : 2*(4*(v+1)-1)≤4*u+8*(v+1)-1 := by omega
    have ha0 : 4*u+8*(v+1)-1≠0 := by omega
    have ha1 : 4*u+8*(v+1)-1≠1 := by omega
    have hk0 : 4*(v+1)-1≠0 := by omega
    simp [secNext,exactSection,ha0,ha1,hk0,hpre]
    omega

/-- Entire all-natural blank-orbit 2D family (1 mod4, 0 mod8) excluded.
    The unique predecessor is forbidden by Agent38's blank mod-four theorem. -/
theorem blank_no_one_eight_family (time u v : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (4*u+1,8*(v+1)) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
            omega
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          rcases p with ⟨a,k⟩
          have ht : secNext (a,k)=some (4*u+1,8*(v+1)) := by
            simpa [BB6.Agent8Section.run,hp] using h
          have he := (section_one_eight_exact a k u v).mp ht
          rcases he with ⟨ha,hk⟩
          have hS : (a+k)%4=2 := by omega
          have hK : k%2=1 := by omega
          have H := BB6Agent38.blank_section_mod4 t a k hp hK hS
          have hA := (Prod.mk.inj H).1
          omega

#print axioms section_one_eight_exact
#print axioms blank_no_one_eight_family
end BB6.Agent15
