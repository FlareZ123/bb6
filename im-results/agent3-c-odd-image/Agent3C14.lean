import Agent3CImage
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem bounce_no_31 (c k : Nat)
    (h : (bounce k c).2=some (3,1)) : False := by
  have hp := BB6Agent38.bounce_positive c k 3 1 h
  omega

private theorem bounce_no_14 (c k : Nat)
    (h : (bounce k c).2=some (1,4)) : False := by
  have hp := bounce_large_image c k 1 4 h (by omega)
  omega

/-- No one-step section output is (3,1). The genuine section start (5,1)
    is a separate exceptional one-counter state. -/
theorem section_no_31 (a k : Nat) :
    secNext (a,k) ≠ some (3,1) := by
  intro h
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2=some (3,1) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        exact bounce_no_31 _ _ hb
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
            · have hb : (bounce 4 (2*k-3)).2=some (3,1) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              exact bounce_no_31 _ _ hb
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (3,1) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          exact bounce_no_31 _ _ hb

/-- An output at (1,4) has exactly one input: (3,1). -/
theorem section_14_requires_31 (a k : Nat)
    (h : secNext (a,k)=some (1,4)) : a=3 ∧ k=1 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2=some (1,4) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        exact False.elim (bounce_no_14 _ _ hb)
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
            · have hb : (bounce 4 (2*k-3)).2=some (1,4) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              exact False.elim (bounce_no_14 _ _ hb)
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (1,4) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          exact False.elim (bounce_no_14 _ _ hb)

/-- The authentic blank-start Machine C section never visits (3,1). -/
theorem blank_no_31 (time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (3,1) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ t =>
    cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at h
    | some p =>
      rcases p with ⟨a,k⟩
      have ht : secNext (a,k)=some (3,1) := by
        simpa [BB6.Agent8Section.run,hp] using h
      exact section_no_31 a k ht

/-- The first dyadic a=1 halting target (1,4), depth zero, is never
    reached by the authentic blank-origin section. -/
theorem blank_no_14 (time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (1,4) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ t =>
    cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at h
    | some p =>
      rcases p with ⟨a,k⟩
      have ht : secNext (a,k)=some (1,4) := by
        simpa [BB6.Agent8Section.run,hp] using h
      obtain ⟨rfl,rfl⟩ := section_14_requires_31 a k ht
      exact blank_no_31 t hp

#print axioms section_no_31
#print axioms section_14_requires_31
#print axioms blank_no_31
#print axioms blank_no_14
end BB6.Agent3
