import SectionAllInverse
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem no_mod16_eight_power (t n : Nat) (ht : 1 ≤ t)
    (h : 16*t+8=2^n*8) : False := by
  cases n with
  | zero => simp at h; omega
  | succ n =>
      rw [Nat.pow_succ] at h
      omega

private theorem pow_two_depth_le_one (t n b : Nat)
    (hb : 4 ∣ b) (h : 16*t+8=2^n*b) : n≤1 := by
  by_cases hn : n≤1
  · exact hn
  have hpow : 4 ∣ 2^n := by
    change 2^2 ∣ 2^n
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hpow
  obtain ⟨v,hv⟩ := hb
  have hdiv : 16 ∣ 16*t+8 := by
    refine ⟨u*v, ?_⟩
    calc
      16*t+8 = 2^n*b := h
      _ = (4*u)*(4*v) := by rw [hu,hv]
      _ = (4*4)*(u*v) := by ac_rfl
      _ = 16*(u*v) := by omega
  omega

/-- For every t>=1, the entire source inverse fiber of (1,16t+7)
    is the single explicit even-first state (8t+2,12t+3). -/
theorem one_seven_parent_only (t a k : Nat) (ht : 1≤t)
    (h : secNext (a,k)=some (1,16*t+7)) :
    a=8*t+2 ∧ k=12*t+3 := by
  have hp := (section_preimage_all_iff a k 1 (16*t+7)).mp h
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at hp
        obtain ⟨_,n,hs,_⟩ := hp
        exact False.elim (no_mod16_eight_power t n ht (by omega))
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
              rcases hp with ⟨he,_⟩ | ⟨_,n,hs,_⟩
              · omega
              · have hdvd : 2 ∣ 2^n*16 := ⟨2^n*8,by omega⟩
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
      · by_cases hlow : 2*k≤a
        · simp [sectionPreimageAll,ha0,ha1,hk0,hlow] at hp
          omega
        · by_cases heven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos heven] at hp
            obtain ⟨_,n,hs,hc⟩ := hp
            have hdivbase : 4 ∣ 2*(a-1)+6 := by
              refine ⟨a/2+1,?_⟩
              omega
            have hdepth : n≤1 := pow_two_depth_le_one t n _ hdivbase (by omega)
            cases n with
            | zero => simp at hs hc; omega
            | succ n =>
                have hn0 : n=0 := by omega
                subst n
                simp [Nat.pow_succ] at hc
                omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg heven] at hp
            rcases hp with ⟨hy,_⟩ | ⟨_,n,hs,_⟩
            · omega
            · have hdiv : 2 ∣ 2^n*(2*(a-1)+8) := by
                refine ⟨2^n*((a-1)+4),?_⟩
                calc
                  2^n*(2*(a-1)+8) = 2^n*(2*((a-1)+4)) := by congr 1 <;> omega
                  _ = 2*(2^n*((a-1)+4)) := by ac_rfl
              omega

#print axioms one_seven_parent_only

/-- This exact target does have its claimed predecessor, in the unmodified
    original section map; the classification is an iff. -/
theorem one_seven_parent_iff (t a k : Nat) (ht : 1≤t) :
    secNext (a,k)=some (1,16*t+7) ↔ a=8*t+2 ∧ k=12*t+3 := by
  constructor
  · exact one_seven_parent_only t a k ht
  · rintro ⟨rfl,rfl⟩
    apply (section_preimage_all_iff _ _ 1 (16*t+7)).mpr
    have ha0 : 8*t+2 ≠0 := by omega
    have ha1 : 8*t+2 ≠1 := by omega
    have hk0 : 12*t+3 ≠0 := by omega
    have hlow : ¬2*(12*t+3)≤8*t+2 := by omega
    have heven : (8*t+2)%2=0 := by omega
    simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow,if_pos heven]
    refine ⟨by omega,0,?_,?_⟩ <;> simp <;> omega

/-- True blank-origin orbit exclusion, at EVERY section time, for an entire
    affine odd-right range. Uses the original image forbidden cone. -/
theorem one_seven_blank_unreachable (t time : Nat) (ht : 1≤t) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (1,16*t+7) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          rcases p with ⟨a,k⟩
          have he : secNext (a,k)=some (1,16*t+7) := by
            simpa [BB6.Agent8Section.run,hp] using h
          obtain ⟨ha,hk⟩ := one_seven_parent_only t a k ht he
          have hh : BB6.Agent8Section.run secNext n (some (5,1)) =
              some (4*(2*t)+2, 4*((3*t)-1+1)+3) := by
            rw [ha,hk] at hp
            have he1 : 4*(2*t)+2=8*t+2 := by omega
            have he2 : 4*((3*t)-1+1)+3=12*t+3 := by omega
            rw [he1,he2]
            exact hp
          exact blank_no_two_three_high n (2*t) (3*t-1) hh

#print axioms one_seven_parent_iff
#print axioms one_seven_blank_unreachable
end BB6.Agent3
