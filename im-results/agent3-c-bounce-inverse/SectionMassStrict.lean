import FastSectionDef
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Every successful even-middle bounce has weighted output at least
    its incoming height plus twice the middle counter and four.
    Crucially this includes the special y=3 exit, which is excluded from
    the earlier y>=5 sum/cost iff. -/
theorem bounce_even_mass_lower (K c x y : Nat) (hK:K%2=0)
    (hb : (bounce K c).2=some (x,y)) :
    c+2*K+4≤x+2*y := by
  induction c using Nat.strongRecOn generalizing K x y with
  | ind c ih =>
    by_cases hlow : c<4
    · simp [bounce,hlow] at hb
    · have hnotodd : K%2≠1 := by omega
      by_cases hc4 : c=4
      · have heq : (x,y)=(2*K+2,3) := by
          have hh:=hb
          rw [bounce] at hh
          simp only [if_neg hlow,if_neg hnotodd,if_pos hc4] at hh
          exact Option.some.inj hh.symm
        obtain ⟨hx,hy⟩ := Prod.mk.inj heq
        subst x; subst y
        omega
      · by_cases hc5 : c=5
        · simp [bounce,hlow,hnotodd,hc4,hc5] at hb
        · by_cases hs : c≤2*K+8
          · have heq : (x,y)=(2*K+8-c,c-1) := by
              have hh:=hb
              rw [bounce] at hh
              simp only [if_neg hlow,if_neg hnotodd,if_neg hc4,if_neg hc5,if_pos hs] at hh
              exact Option.some.inj hh.symm
            obtain ⟨hx,hy⟩ := Prod.mk.inj heq
            subst x; subst y
            omega
          · have hlt : c-(2*K+5)<c := by omega
            have hh : (bounce (2*K+4) (c-(2*K+5))).2=some (x,y) := by
              have hc:=hb
              rw [bounce] at hc
              simpa only [if_neg hlow,if_neg hnotodd,if_neg hc4,if_neg hc5,if_neg hs] using hc
            have hi := ih (c-(2*K+5)) hlt (2*K+4) x y (by omega) hh
            omega

/-- A successful odd-middle bounce obeys the sharper analogous inequality. -/
theorem bounce_odd_mass_lower (K c x y : Nat) (hK:K%2=1)
    (hb : (bounce K c).2=some (x,y)) :
    c+2*K+6≤x+2*y := by
  induction c using Nat.strongRecOn generalizing K x y with
  | ind c ih =>
    by_cases hlow : c<4
    · simp [bounce,hlow] at hb
    · by_cases hs : c≤2*K+6
      · have heq : (x,y)=(2*K+6-c,c) := by
          have hh:=hb
          rw [bounce] at hh
          simp only [if_neg hlow,if_pos hK,if_pos hs] at hh
          exact Option.some.inj hh.symm
        obtain ⟨hx,hy⟩ := Prod.mk.inj heq
        subst x; subst y
        omega
      · have hlt : c-(2*K+3)<c := by omega
        have hh : (bounce (2*K+3) (c-(2*K+3))).2=some (x,y) := by
          have hc:=hb
          rw [bounce] at hc
          simpa only [if_neg hlow,if_pos hK,if_neg hs] using hc
        have hi := ih (c-(2*K+3)) hlt (2*K+3) x y (by omega) hh
        omega

/-- Every successful original Machine C first-return step strictly
    increases the integer weight a+2k by at least TWO.
    This includes all exceptional source branches, all recursive
    bounce paths, and the y=3 terminal branch. -/
theorem section_mass_strict (a k x y : Nat)
    (h : secNext (a,k)=some (x,y)) :
    a+2*k+2≤x+2*y := by
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
      · by_cases hlow : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hlow] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow] using h
          by_cases he : a%2=0
          · have hh := bounce_odd_mass_lower (a-1) (2*k-a+3) x y (by omega) hb
            omega
          · have hh := bounce_even_mass_lower (a-1) (2*k-a+3) x y (by omega) hb
            omega

#print axioms bounce_even_mass_lower
#print axioms bounce_odd_mass_lower
#print axioms section_mass_strict
end BB6.Agent46
