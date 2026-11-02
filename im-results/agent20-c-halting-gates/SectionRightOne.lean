import Agent38SectionParity
import SectionAffineInverse
import Lean.Elab.Tactic.Omega

namespace Agent20Gate
open BB6.Agent46

/-- The unique direct source of a Machine C two-counter section with right
    counter one is (1,0), and its output is (5,1). -/
theorem section_one_source (a k x : Nat)
    (h : secNext (a,k)=some (x,1)) : a=1 ∧ k=0 ∧ x=5 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2=some (x,1) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        have hh := BB6Agent38.bounce_positive _ _ _ _ hb
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        exact ⟨ha1,hk0,by omega⟩
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
            · have hb : (bounce 4 (2*k-3)).2=some (x,1) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              have hh := BB6Agent38.bounce_positive _ _ _ _ hb
              omega
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,1) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          have hh := BB6Agent38.bounce_positive _ _ _ _ hb
          omega

/-- The blank-origin Machine C section has right counter one only at the
    exact initial section state (5,1), never on a positive section return. -/
theorem blank_right_one_iff_initial (time a : Nat)
    (hr : BB6.Agent8Section.run secNext time (some (5,1))=some (a,1)) :
    time=0 ∧ a=5 := by
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hr
      omega
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at hr
      | some p =>
          rcases p with ⟨u,v⟩
          have ht : secNext (u,v)=some (a,1) := by
            simpa [BB6.Agent8Section.run,hp] using hr
          obtain ⟨_,hv,_⟩ := section_one_source u v a ht
          have hpositive := BB6Agent38.blank_section_positive t u v hp
          omega

/-- The smallest low halting gateway (1,4) has exactly the unreachable
    predecessor (3,1), removing the one low-branch exponent m=0. -/
theorem blank_no_low_zero (time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (1,4) := by
  intro hr
  cases time with
  | zero => simp [BB6.Agent8Section.run] at hr
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at hr
      | some p =>
          rcases p with ⟨a,k⟩
          have ht : secNext (a,k)=some (1,4) := by
            simpa [BB6.Agent8Section.run,hp] using hr
          have hpred := (BB6.Agent15.section_sum_one_even_iff_affine a k 1 4
            (by decide) (by decide) (by decide)).mp ht
          rcases hpred with ⟨ha,hk⟩
          have hprev : BB6.Agent8Section.run secNext t (some (5,1))=some (3,1) := by
            rw [ha,hk] at hp
            simpa using hp
          have hh := blank_right_one_iff_initial t 3 hprev
          omega

#print axioms section_one_source
#print axioms blank_right_one_iff_initial
#print axioms blank_no_low_zero
end Agent20Gate
