import FastSectionDef
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6Agent38

open BB6.Agent46

theorem bounce_mod4_pos (c k x y : Nat)
    (h : (bounce k c).2 = some (x,y)) : (x+y)%4≠2 ∧ 3≤y := by
  induction c using Nat.strongRecOn generalizing k x y with
  | ind c ih =>
    by_cases hlow : c < 4
    · simp [bounce,hlow] at h
    · by_cases hk : k % 2 = 1
      · by_cases hsmall : c ≤ 2*k+6
        · have heq : (x,y) = (2*k+6-c,c) := by
            have hh := h
            rw [bounce] at hh
            simp only [if_neg hlow, if_pos hk, if_pos hsmall] at hh
            exact Option.some.inj hh.symm
          cases Prod.mk.inj heq with
          | intro hx hy =>
            subst x; subst y
            have hpos : c≤2*k+6 := hsmall
            omega
        · have hlt : c-(2*k+3)<c := by omega
          have hh : (bounce (2*k+3) (c-(2*k+3))).2=some (x,y) := by
            have hc := h
            rw [bounce] at hc
            simpa only [if_neg hlow,if_pos hk,if_neg hsmall] using hc
          exact ih _ hlt _ _ _ hh
      · by_cases h4 : c=4
        · subst c
          have heq : (x,y)=(2*k+2,3) := by
            have hh := h
            rw [bounce] at hh
            simp only [if_neg hlow, if_neg hk,if_pos rfl] at hh
            exact Option.some.inj hh.symm
          cases Prod.mk.inj heq with
          | intro hx hy =>
            subst x; subst y
            omega
        · by_cases h5 : c=5
          · simp [bounce,hlow,hk,h4,h5] at h
          · by_cases hsmall : c ≤ 2*k+8
            · have heq : (x,y)=(2*k+8-c,c-1) := by
                have hh:=h
                rw [bounce] at hh
                simp only [if_neg hlow,if_neg hk,if_neg h4,if_neg h5,if_pos hsmall] at hh
                exact Option.some.inj hh.symm
              cases Prod.mk.inj heq with
              | intro hx hy =>
                subst x; subst y
                omega
            · have hlt : c-(2*k+5)<c := by omega
              have hh : (bounce (2*k+4) (c-(2*k+5))).2=some (x,y) := by
                have hc := h
                rw [bounce] at hc
                simpa only [if_neg hlow,if_neg hk,if_neg h4,if_neg h5,if_neg hsmall] using hc
              exact ih _ hlt _ _ _ hh

theorem bounce_mod4 (c k x y : Nat)
    (h : (bounce k c).2 = some (x,y)) : (x+y)%4≠2 :=
  (bounce_mod4_pos c k x y h).1

theorem bounce_positive (c k x y : Nat)
    (h : (bounce k c).2 = some (x,y)) : 3≤y :=
  (bounce_mod4_pos c k x y h).2

theorem section_output_mod4 (a k x y : Nat)
    (h : secNext (a,k) = some (x,y))
    (hy : y%2=1) (hs : (x+y)%4=2) : (x,y)=(5,1) := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
        omega
      · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        exact False.elim ((bounce_mod4 _ _ _ _ hb) hs)
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        rcases h with ⟨hx,hyEq⟩
        subst x
        subst y
        rfl
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
              exact False.elim ((bounce_mod4 _ _ _ _ hb) hs)
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          exact False.elim ((bounce_mod4 _ _ _ _ hb) hs)

theorem section_output_positive (a k x y : Nat)
    (h : secNext (a,k) = some (x,y)) : 1≤y := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
        omega
      · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        exact Nat.le_trans (by omega : 1≤3) (bounce_positive _ _ _ _ hb)
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
              exact Nat.le_trans (by omega : 1≤3) (bounce_positive _ _ _ _ hb)
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          exact Nat.le_trans (by omega : 1≤3) (bounce_positive _ _ _ _ hb)

theorem section_51_only_from_10 (a k : Nat)
    (h : secNext (a,k) = some (5,1)) : a=1 ∧ k=0 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2 = some (5,1) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        have hh := bounce_mod4 _ _ _ _ hb
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · exact ⟨ha1,hk0⟩
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
            · have hb : (bounce 4 (2*k-3)).2 = some (5,1) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              have hh := bounce_mod4 _ _ _ _ hb
              omega
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
        · have hb : (bounce (a-1) (2*k-a+3)).2 = some (5,1) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          have hh := bounce_mod4 _ _ _ _ hb
          omega

theorem blank_section_mod4 (n x y : Nat)
    (h : BB6.Agent8Section.run secNext n (some (5,1)) = some (x,y))
    (hy : y%2=1) (hs : (x+y)%4=2) : (x,y)=(5,1) := by
  cases n with
  | zero =>
    simpa [BB6.Agent8Section.run] using (Option.some.inj h.symm)
  | succ n =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none =>
      simp [BB6.Agent8Section.run,hp] at h
    | some p =>
      rcases p with ⟨a,k⟩
      have ht : secNext (a,k) = some (x,y) := by
        simpa [BB6.Agent8Section.run,hp] using h
      exact section_output_mod4 a k x y ht hy hs

theorem blank_section_positive (n a k : Nat)
    (h : BB6.Agent8Section.run secNext n (some (5,1)) = some (a,k)) : 1≤k := by
  cases n with
  | zero =>
    simp [BB6.Agent8Section.run] at h
    omega
  | succ n =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at h
    | some p =>
      rcases p with ⟨u,v⟩
      have ht : secNext (u,v)=some (a,k) := by
        simpa [BB6.Agent8Section.run,hp] using h
      exact section_output_positive u v a k ht

theorem blank_section_no_51_return (n : Nat) :
    BB6.Agent8Section.run secNext (n+1) (some (5,1)) ≠ some (5,1) := by
  intro h
  cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
  | none => simp [BB6.Agent8Section.run,hp] at h
  | some p =>
    rcases p with ⟨a,k⟩
    have ht : secNext (a,k) = some (5,1) := by
      simpa [BB6.Agent8Section.run,hp] using h
    have hpred := section_51_only_from_10 a k ht
    have hpos := blank_section_positive n a k hp
    omega

theorem blank_section_strict_mod4 (n a k : Nat)
    (h : BB6.Agent8Section.run secNext (n+1) (some (5,1)) = some (a,k))
    (hy : k%2=1) : (a+k)%4≠2 := by
  intro hm
  have he := blank_section_mod4 (n+1) a k h hy hm
  have hret := blank_section_no_51_return n
  rw [he] at h
  exact hret h

theorem blank_section_no_33 (n a k : Nat) :
  BB6.Agent8Section.run secNext n (some (5,1)) ≠ some (4*a+3,4*k+3) := by
  intro h
  have he := blank_section_mod4 n (4*a+3) (4*k+3) h (by omega) (by omega)
  have hfirst := (Prod.mk.inj he).1
  omega

#print axioms blank_section_strict_mod4
#print axioms blank_section_no_51_return
#print axioms blank_section_mod4
#print axioms blank_section_no_33
#print axioms bounce_mod4
#print axioms section_output_mod4
end BB6Agent38
