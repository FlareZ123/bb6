import Low267Arithmetic
import FullSectionInverse
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace BB6.Agent38Low267

/-- Source-exhaustive two-predecessor classification of the 267-ray feeder. -/
theorem r_parent_criterion (q a k : Nat)
    (h : BB6.Agent46.sectionPreimageCriterion a k (832*q+424) (96*q+48)) :
    (a=232*q+116 ∧ k=396*q+197) ∨
    (a=928*q+470 ∧ k=48*q+23) := by
  unfold BB6.Agent46.sectionPreimageCriterion at h
  by_cases ha0 : a=0
  · simp only [if_pos ha0] at h
    by_cases hk0 : k=0
    · simp [hk0] at h
    · by_cases hk1 : k=1
      · simp [hk0,hk1] at h
      · simp only [if_neg hk0,if_neg hk1] at h
        obtain ⟨n,hs,_⟩ := h
        have heq : 928*q+472=2^n*8 := by omega
        exact False.elim (no_zero_branch q n heq)
  · by_cases ha1 : a=1
    · simp only [if_neg ha0,if_pos ha1] at h
      by_cases hk0 : k=0
      · simp [hk0] at h
      · by_cases hk1 : k=1
        · simp [hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [hk0,hk1,hk2,hk3] at h
            · simp only [if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              obtain ⟨n,hs,_⟩ := h
              have he : 928*q+473=2^n*16 := by omega
              let v := 2^n
              change 928*q+473=v*16 at he
              omega
    · have ha2 : 2≤a := by omega
      simp only [if_neg ha0, if_neg ha1] at h
      by_cases hk0 : k=0
      · simp [hk0] at h
      · simp only [if_neg hk0] at h
        by_cases hregion : 2*k≤a
        · simp only [if_pos hregion] at h
          rcases h with ⟨hx,hy⟩
          right
          omega
        · simp only [if_neg hregion] at h
          by_cases hae : a%2=0
          · simp only [if_pos hae] at h
            obtain ⟨n,hs,hc⟩ := h
            have hs' : 928*q+472=2^n*(2*(a-1)+6) := by omega
            have hc' : (2*k-a+3)+(2*(a-1)+6)+3*n=1024*q+520 := by omega
            left
            exact even_bounce_generic q a k n ha2 hae (by omega) hs' hc'
          · simp only [if_neg hae] at h
            obtain ⟨n,hs,_⟩ := h
            have hodd : 928*q+473=2^n*(2*(a-1)+8) := by omega
            have hev : 2 ∣ 2^n*(2*(a-1)+8) := by
              refine ⟨2^n*(a-1+4), ?_⟩
              have heq : 2*(a-1)+8=2*(a-1+4) := by omega
              rw [heq]
              ac_rfl
            rcases hev with ⟨v,hv⟩
            omega

/-- Every real section edge into R(q) must come from one of two
    parameterized sources. Includes all exceptional and recursive cases. -/
theorem r_parent_source (q a k : Nat)
    (h : BB6.Agent46.secNext (a,k)=some (832*q+424,96*q+48)) :
    (a=232*q+116 ∧ k=396*q+197) ∨
    (a=928*q+470 ∧ k=48*q+23) := by
  have hi := (BB6.Agent46.complete_section_inverse a k
    (832*q+424) (96*q+48) (by omega)).mp h
  exact r_parent_criterion q a k hi

#print axioms r_parent_source
end BB6.Agent38Low267
