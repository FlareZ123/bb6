import FastSectionDef
import Lean.Elab.Tactic.Omega

namespace BB6Agent34
open BB6.Agent46

/-- Every genuine bounce with second output >=5 avoids sum residue 1 modulo 4. -/
theorem bounce_no_sum_one_large (c k x y : Nat)
    (h : (bounce k c).2 = some (x,y)) (hy : 4≤y) : (x+y)%4 ≠ 1 := by
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
          | intro hx hyEq =>
            subst x; subst y
            omega
        · have hlt : c-(2*k+3)<c := by omega
          have hh : (bounce (2*k+3) (c-(2*k+3))).2=some (x,y) := by
            have hc := h
            rw [bounce] at hc
            simpa only [if_neg hlow,if_pos hk,if_neg hsmall] using hc
          exact ih _ hlt _ _ _ hh hy
      · by_cases h4 : c=4
        · subst c
          have heq : (x,y)=(2*k+2,3) := by
            have hh := h
            rw [bounce] at hh
            simp only [if_neg hlow, if_neg hk,if_pos rfl] at hh
            exact Option.some.inj hh.symm
          cases Prod.mk.inj heq with
          | intro hx hyEq =>
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
              | intro hx hyEq =>
                subst x; subst y
                omega
            · have hlt : c-(2*k+5)<c := by omega
              have hh : (bounce (2*k+4) (c-(2*k+5))).2=some (x,y) := by
                have hc := h
                rw [bounce] at hc
                simpa only [if_neg hlow,if_neg hk,if_neg h4,if_neg h5,if_neg hsmall] using hc
              exact ih _ hlt _ _ _ hh hy

/-- Exact original section image excludes odd y>=5 with x+y ≡1 (mod4). -/
theorem section_no_sum_one_large_odd (a k x y : Nat)
    (h : secNext (a,k) = some (x,y))
    (hy : 5≤y) (hodd : y%2=1) : (x+y)%4 ≠ 1 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
        omega
      · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        exact bounce_no_sum_one_large _ _ _ _ hb (by omega)
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
              exact bounce_no_sum_one_large _ _ _ _ hb (by omega)
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          exact bounce_no_sum_one_large _ _ _ _ hb (by omega)


/-- Every (1,y) with y>=4 divisible by four has only the unique
    possible direct-branch source. This holds for arbitrary source (a,k). -/
theorem one_four_target_only_direct (a k y : Nat)
    (h : secNext (a,k)=some (1,y)) (hy:4≤y) (hfour:y%4=0) :
    a=y-1 ∧ 2*k+2=y := by
  have hsum : (1+y)%4=1 := by omega
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2=some (1,y) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        exact False.elim ((bounce_no_sum_one_large _ _ _ _ hb hy) hsum)
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
            · have hb : (bounce 4 (2*k-3)).2=some (1,y) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              exact False.elim ((bounce_no_sum_one_large _ _ _ _ hb hy) hsum)
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (1,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          exact False.elim ((bounce_no_sum_one_large _ _ _ _ hb hy) hsum)

#print axioms one_four_target_only_direct

#print axioms bounce_no_sum_one_large
#print axioms section_no_sum_one_large_odd
end BB6Agent34
