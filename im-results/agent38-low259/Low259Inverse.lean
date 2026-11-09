import Low259Arithmetic
import FullSectionInverse
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace BB6.Agent38Low259

/-- The full original section inverse grammar has exactly these three
    possible parents of the two-counter ray P(q). -/
theorem p_parent_criterion (q a k : Nat)
    (h : BB6.Agent46.sectionPreimageCriterion a k (256*q+128) (384*q+192)) :
    (a=40*q+18 ∧ k=492*q+239) ∨
    (a=160*q+78 ∧ k=432*q+212) ∨
    (a=640*q+318 ∧ k=192*q+95) := by
  unfold BB6.Agent46.sectionPreimageCriterion at h
  by_cases ha0 : a=0
  · simp only [if_pos ha0] at h
    by_cases hk0 : k=0
    · simp [hk0] at h
    · by_cases hk1 : k=1
      · simp [hk0,hk1] at h
      · simp only [if_neg hk0,if_neg hk1] at h
        obtain ⟨n,hs,_⟩ := h
        have heq : 640*q+320=8*(2:Nat)^n := by
          calc
            640*q+320=(256*q+128)+(384*q+192) := by omega
            _=2^n*8 := hs
            _=8*2^n := by ac_rfl
        exact False.elim (pow_no_zero_branch q n heq)
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
              have he : 640*q+321=2^n*16 := by omega
              let v := 2^n
              change 640*q+321=v*16 at he
              omega
    · have ha2 : 2≤a := by omega
      simp only [if_neg ha0, if_neg ha1] at h
      by_cases hk0 : k=0
      · simp [hk0] at h
      · simp only [if_neg hk0] at h
        by_cases hregion : 2*k≤a
        · simp only [if_pos hregion] at h
          rcases h with ⟨hx,hy⟩
          right;right
          omega
        · simp only [if_neg hregion] at h
          by_cases hae : a%2=0
          · simp only [if_pos hae] at h
            obtain ⟨n,hs,hc⟩ := h
            have hs' : 640*q+320=2^n*(2*(a-1)+6) := by omega
            have hc' : (2*k-a+3)+(2*(a-1)+6)+3*n=1024*q+512 := by omega
            rcases generic_even_bounce_inverse q a k n ha2 hae (by omega) hs' hc' with hQ | hF
            · exact Or.inr (Or.inl hQ)
            · exact Or.inl hF
          · simp only [if_neg hae] at h
            obtain ⟨n,hs,_⟩ := h
            have hodd : 640*q+321=2^n*(2*(a-1)+8) := by omega
            have hev : 2 ∣ 2^n*(2*(a-1)+8) := by
              refine ⟨2^n*(a-1+4), ?_⟩
              have heq : 2*(a-1)+8=2*(a-1+4) := by omega
              rw [heq]
              ac_rfl
            rcases hev with ⟨v,hv⟩
            omega

/-- Original-source edge classification; no abstract quotient premises. -/
theorem p_parent_source (q a k : Nat)
    (h : BB6.Agent46.secNext (a,k)=some (256*q+128,384*q+192)) :
    (a=40*q+18 ∧ k=492*q+239) ∨
    (a=160*q+78 ∧ k=432*q+212) ∨
    (a=640*q+318 ∧ k=192*q+95) := by
  have hi := (BB6.Agent46.complete_section_inverse a k (256*q+128)
    (384*q+192) (by omega)).mp h
  exact p_parent_criterion q a k hi

#print axioms p_parent_source
end BB6.Agent38Low259
