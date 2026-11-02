import FastSectionDef
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- All odd, non-small outputs of the complete recursive bounce lie on
    just two of the four sum residues, independently of their inputs. -/
theorem bounce_odd_image (c k x y : Nat)
    (h : (bounce k c).2 = some (x,y))
    (hy : 5 ≤ y) (ho : y%2=1) :
    (x+y)%4=0 ∨ (x+y)%4=3 := by
  induction c using Nat.strongRecOn generalizing k x y with
  | ind c ih =>
    by_cases hlow : c < 4
    · simp [bounce, hlow] at h
    · by_cases hk : k%2=1
      · by_cases hsmall : c ≤ 2*k+6
        · have heq : (x,y)=(2*k+6-c,c) := by
            have hh := h
            rw [bounce] at hh
            simp only [if_neg hlow,if_pos hk,if_pos hsmall] at hh
            exact Option.some.inj hh.symm
          cases Prod.mk.inj heq with
          | intro hx hyEq =>
            subst x; subst y
            omega
        · have hlt : c-(2*k+3)<c := by omega
          have hh : (bounce (2*k+3) (c-(2*k+3))).2=some (x,y) := by
            have hc := h
            rw [bounce] at hc
            simpa only [if_neg hlow,if_pos hk,if_neg hsmall] using hc
          exact ih _ hlt _ _ _ hh hy ho
      · by_cases h4 : c=4
        · subst c
          have heq : (x,y)=(2*k+2,3) := by
            have hh:=h
            rw [bounce] at hh
            simp only [if_neg hlow,if_neg hk,if_pos rfl] at hh
            exact Option.some.inj hh.symm
          cases Prod.mk.inj heq with
          | intro hx hyEq =>
            subst x; subst y
            omega
        · by_cases h5 : c=5
          · simp [bounce, hlow, hk, h4, h5] at h
          · by_cases hsmall : c ≤ 2*k+8
            · have heq : (x,y)=(2*k+8-c,c-1) := by
                have hh:=h
                rw [bounce] at hh
                simp only [if_neg hlow,if_neg hk,if_neg h4,if_neg h5,if_pos hsmall] at hh
                exact Option.some.inj hh.symm
              cases Prod.mk.inj heq with
              | intro hx hyEq =>
                subst x; subst y
                omega
            · have hlt : c-(2*k+5)<c := by omega
              have hh : (bounce (2*k+4) (c-(2*k+5))).2=some (x,y) := by
                have hc := h
                rw [bounce] at hc
                simpa only [if_neg hlow,if_neg hk,if_neg h4,if_neg h5,if_neg hsmall] using hc
              exact ih _ hlt _ _ _ hh hy ho

/-- For every source state, a successful section return with odd
    second coordinate at least five has sum residue 0 or 3 modulo 4. -/
theorem section_odd_image (a k x y : Nat)
    (h : secNext (a,k)=some (x,y))
    (hy : 5≤y) (ho : y%2=1) :
    (x+y)%4=0 ∨ (x+y)%4=3 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
        omega
      · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        exact bounce_odd_image _ _ _ _ hb hy ho
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
              exact bounce_odd_image _ _ _ _ hb hy ho
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          exact bounce_odd_image _ _ _ _ hb hy ho

/-- Every post-initial successful section orbit state with an odd second
    coordinate at least five belongs to a two-residue support. -/
theorem blank_section_odd_image (time x y : Nat)
    (h : BB6.Agent8Section.run secNext (time+1) (some (5,1)) = some (x,y))
    (hy : 5≤y) (ho : y%2=1) :
    (x+y)%4=0 ∨ (x+y)%4=3 := by
  cases hp : BB6.Agent8Section.run secNext time (some (5,1)) with
  | none => simp [BB6.Agent8Section.run,hp] at h
  | some p =>
    rcases p with ⟨a,k⟩
    have ht : secNext (a,k)=some (x,y) := by
      simpa [BB6.Agent8Section.run,hp] using h
    exact section_odd_image a k x y ht hy ho

/-- A new infinite, globally forbidden section family: an even first
    coordinate congruent 2 modulo 4 cannot be paired with an odd second
    coordinate congruent 3 modulo 4 once the latter is at least 7. -/
theorem blank_no_two_three_high (time u v : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (4*u+2,4*(v+1)+3) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ n =>
    have hr := blank_section_odd_image n (4*u+2) (4*(v+1)+3) h
      (by omega) (by omega)
    omega

#print axioms blank_no_two_three_high
#print axioms blank_section_odd_image
#print axioms bounce_odd_image
#print axioms section_odd_image
end BB6.Agent3
