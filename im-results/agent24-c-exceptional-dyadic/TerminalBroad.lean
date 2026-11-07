import TerminalCone
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46
set_option maxRecDepth 8192

/-- Generalized full original source inverse exclusion across two congruence rectangles. -/
theorem exceptional_parent_all (a k X Y : Nat)
    (hX : X%8=3) (hY : Y%8=4) (hV : (X+Y+1)%32=24) (hy : 12≤Y)
    (he : secNext (a,k)=some (X,Y)) :
    5≤k ∧ k%2=1 ∧ (a+k)%4=2 := by
  have hY12 : 12≤Y := hy
  have h := (complete_section_inverse a k X Y (by omega)).mp he
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageCriterion,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [sectionPreimageCriterion,ha0,hk0,hk1] at h
        omega
      · obtain ⟨n,hs,hcost⟩ :
            ∃ n : Nat, X+Y=2^n*8 ∧ (2*k+1)+8+3*n=X+2*Y := by
          simpa [sectionPreimageCriterion,ha0,hk0,hk1] using h
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
      · by_cases hk1 : k=1
        · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2] at h
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · obtain ⟨n,hs,hc⟩ :
                  ∃ n : Nat, X+Y+1=2^n*16 ∧
                    (2*k-3)+16+3*n=X+2*Y+2 := by
                simpa [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] using h
              have hdiv : 16 ∣ X+Y+1 := ⟨2^n,by omega⟩
              have hmod : (X+Y+1)%16=0 := Nat.mod_eq_zero_of_dvd hdiv
              omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
      · by_cases hregion : 2*k≤a
        · obtain ⟨hx,hy⟩ : X=a-2*k ∧ Y=2*k+2 := by
            simpa [sectionPreimageCriterion,ha0,ha1,hk0,hregion] using h
          omega
        · by_cases haeven : a%2=0
          · obtain ⟨n,hs,hc⟩ :
                ∃ n : Nat, X+Y=2^n*(2*(a-1)+6) ∧
                  (2*k-a+3)+(2*(a-1)+6)+3*n=X+2*Y := by
              simpa [sectionPreimageCriterion,ha0,ha1,hk0,hregion,haeven] using h
            have hcoef : 2*(a-1)+6=2*(a+2) := by omega
            rw [hcoef] at hs
            have heven : 2∣X+Y := by
              refine ⟨2^n*(a+2),?_⟩
              rw [hs]
              ac_rfl
            have hmod : (X+Y)%2=0 := Nat.mod_eq_zero_of_dvd heven
            omega
          · obtain ⟨n,hs,hc⟩ :
                ∃ n : Nat, X+Y+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=X+2*Y+2 := by
              simpa [sectionPreimageCriterion,ha0,ha1,hk0,hregion,haeven] using h
            by_cases hn0 : n=0
            · subst n
              simp at hs hc
              omega
            · by_cases hn1 : n=1
              · subst n
                simp at hs hc
                omega
              · have hn2 : 2≤n := by omega
                have hpow : 4∣2^n := by
                  simpa using (Nat.pow_dvd_pow 2 hn2)
                obtain ⟨b,hb⟩ := hpow
                obtain ⟨c,hac⟩ : ∃ c : Nat, 2*(a-1)+8=4*c := by
                  refine ⟨(a+3)/2,?_⟩
                  omega
                have hdiv : 16 ∣ X+Y+1 := by
                  refine ⟨b*c,?_⟩
                  rw [hs,hb,hac]
                  ac_rfl
                have hmod : (X+Y+1)%16=0 := Nat.mod_eq_zero_of_dvd hdiv
                omega


/-- Infinite all-time blank-root exclusion for the broad exceptional sector. -/
theorem exceptional_no_blank_all (X Y : Nat) (hX:X%8=3) (hY:Y%8=4)
    (hV:(X+Y+1)%32=24) (hy:12≤Y) : ¬ BB6.Agent3.CReach X Y := by
  rintro ⟨time,hrt⟩
  cases time with
  | zero =>
    simp [BB6.Agent8Section.run] at hrt
    omega
  | succ n =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at hrt
    | some p =>
      rcases p with ⟨a,k⟩
      have hedge : secNext (a,k)=some (X,Y) := by
        simpa [BB6.Agent8Section.run,hp] using hrt
      obtain ⟨hk,hodd,hsum⟩ :=
        exceptional_parent_all a k X Y hX hY hV hy hedge
      cases n with
      | zero =>
        simp [BB6.Agent8Section.run] at hp
        omega
      | succ m =>
        have hmod := BB6.Agent3.blank_section_odd_image m a k hp hk hodd
        omega

#print axioms exceptional_parent_all
#print axioms exceptional_no_blank_all
end BB6.Agent46
