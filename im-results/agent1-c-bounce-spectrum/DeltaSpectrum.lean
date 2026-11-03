import FastSectionDef
import BounceInverse
import EvenThree
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- No successful section transition with positive initial right counter
  can increase weighted mass by 8,14,20,..., even after arbitrary
  recursive odd/even bounce chains. -/
theorem section_no_gain_8_plus_6r (a k x y r : Nat)
    (hk : 0<k) (h : secNext (a,k)=some (x,y)) :
    x+2*y ≠ a+2*k+8+6*r := by
  intro hbad
  by_cases ha0 : a=0
  · by_cases hk1 : k=1
    · simp [secNext,exactSection,ha0,hk1] at h
      omega
    · have hb : (bounce 1 (2*k+1)).2 =some (x,y) := by
        have hk0 : k≠0 := by omega
        simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
      obtain ⟨n, hsum, hcost⟩ :=
        bounce_odd_output_invariants (2*k+1) 1 x y (by decide) hb
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
            have hy := bounce_even_y_ge_three (2*k-3) 4 x y (by decide) hb
            by_cases h4 : 4≤y
            · obtain ⟨n, _, hcost⟩ := bounce_even_output_invariants (2*k-3) 4 x y (by decide) h4 hb
              omega
            · have hy3 : y=3 := by omega
              subst y
              obtain ⟨n, hcost, hpar⟩ := bounce_even_three_cost (2*k-3) 4 x (by decide) hb
              omega
    · have hk0 : k≠0 := by omega
      by_cases hlow : 2*k≤a
      · simp [secNext,exactSection,ha0,ha1,hk0,hlow] at h
        omega
      · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow] using h
        by_cases he : a%2=0
        · obtain ⟨n, _, hcost⟩ := bounce_odd_output_invariants (2*k-a+3) (a-1) x y (by omega) hb
          omega
        · have hy := bounce_even_y_ge_three (2*k-a+3) (a-1) x y (by omega) hb
          by_cases h4 : 4≤y
          · obtain ⟨n, _, hcost⟩ := bounce_even_output_invariants (2*k-a+3) (a-1) x y (by omega) h4 hb
            omega
          · have hy3 : y=3 := by omega
            subst y
            obtain ⟨n, hcost, hpar⟩ := bounce_even_three_cost (2*k-a+3) (a-1) x (by omega) hb
            omega

#print axioms section_no_gain_8_plus_6r
end BB6.Agent46
