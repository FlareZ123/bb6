import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6Agent38
open BB6.Agent46

/-- No successful recursive bounce outputs first-coordinate 1 mod 4
    and second-coordinate 0 mod 8 simultaneously. -/
theorem bounce_no_one8 (c k x y : Nat)
    (h : (bounce k c).2=some (x,y)) : x%4≠1 ∨ y%8≠0 := by
  induction c using Nat.strongRecOn generalizing k x y with
  | ind c ih =>
    by_cases hlow : c<4
    · simp [bounce,hlow] at h
    · by_cases hk : k%2=1
      · by_cases hsmall : c≤2*k+6
        · have heq : (x,y)=(2*k+6-c,c) := by
            have hh := h
            rw [bounce] at hh
            simp only [if_neg hlow,if_pos hk,if_pos hsmall] at hh
            exact Option.some.inj hh.symm
          cases Prod.mk.inj heq with
          | intro hx hy =>
            subst x;subst y
            omega
        · have hlt : c-(2*k+3)<c := by omega
          have hh : (bounce (2*k+3) (c-(2*k+3))).2=some (x,y) := by
            have hc:=h
            rw [bounce] at hc
            simpa only [if_neg hlow,if_pos hk,if_neg hsmall] using hc
          exact ih _ hlt _ _ _ hh
      · by_cases h4 : c=4
        · subst c
          have heq : (x,y)=(2*k+2,3) := by
            have hh:=h
            rw [bounce] at hh
            simp only [if_neg hlow,if_neg hk,if_pos rfl] at hh
            exact Option.some.inj hh.symm
          cases Prod.mk.inj heq with
          | intro hx hy =>
            subst x; subst y
            omega
        · by_cases h5 : c=5
          · simp [bounce,hlow,hk,h4,h5] at h
          · by_cases hsmall : c≤2*k+8
            · have heq : (x,y)=(2*k+8-c,c-1) := by
                have hh:=h
                rw [bounce] at hh
                simp only [if_neg hlow,if_neg hk,if_neg h4,if_neg h5,if_pos hsmall] at hh
                exact Option.some.inj hh.symm
              cases Prod.mk.inj heq with
              | intro hx hy =>
                subst x;subst y
                omega
            · have hlt : c-(2*k+5)<c := by omega
              have hh : (bounce (2*k+4) (c-(2*k+5))).2=some (x,y) := by
                have hc:=h
                rw [bounce] at hc
                simpa only [if_neg hlow,if_neg hk,if_neg h4,if_neg h5,if_neg hsmall] using hc
              exact ih _ hlt _ _ _ hh

/-- Any one-mod-four, eight-divisible section output can only
    originate in a three/three-mod-four section input. -/
theorem section_output_one8_predecessor (a k x y : Nat)
    (h : secNext (a,k)=some (x,y))
    (hx : x%4=1) (hy : y%8=0) : a%4=3 ∧ k%4=3 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
        omega
      · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        have hh := bounce_no_one8 _ _ _ _ hb
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
              have hh := bounce_no_one8 _ _ _ _ hb
              omega
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          have hh := bounce_no_one8 _ _ _ _ hb
          omega

/-- A second-stage blank-origin restriction obtained by chaining
    the universal output classification to the global 3/3 exclusion. -/
theorem blank_section_no_one8 (time a k : Nat)
    (ha : a%4=1) (hk : k%8=0) :
    BB6.Agent8Section.run secNext time (some (5,1))≠some (a,k) := by
  intro hs
  cases time with
  | zero =>
    simp [BB6.Agent8Section.run] at hs
    omega
  | succ n =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at hs
    | some p =>
      rcases p with ⟨u,v⟩
      have ht : secNext (u,v)=some (a,k) := by
        simpa [BB6.Agent8Section.run,hp] using hs
      have hpred := section_output_one8_predecessor u v a k ht ha hk
      have hno := blank_section_no_33 n (u/4) (v/4)
      have heq : (u,v)=(4*(u/4)+3,4*(v/4)+3) := by
        apply Prod.ext
        · omega
        · omega
      rw [heq] at hp
      exact hno hp

#print axioms bounce_no_one8
#print axioms section_output_one8_predecessor
#print axioms blank_section_no_one8

end BB6Agent38
