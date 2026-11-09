import SectionAllInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Three
open BB6.Agent46

private theorem mul_even (a n : Nat) : 2 ∣ 2^n * (2*(a-1)+6) := by
  refine ⟨2^n * ((a-1)+3), ?_⟩
  have h : 2*(a-1)+6=2*((a-1)+3) := by omega
  rw [h]
  ac_rfl

private theorem mul_four_odd (a n : Nat) (ha : a%2=1) :
    4 ∣ 2^n * (2*(a-1)+8) := by
  have he : 4 ∣ 2*(a-1)+8 := by
    refine ⟨(a-1)/2+2, ?_⟩
    omega
  rcases he with ⟨q,hq⟩
  refine ⟨2^n*q,?_⟩
  rw [hq]
  ac_rfl

private theorem mul_eight_even (a n : Nat) (ha : a%2=0) (hb : 2≤a) (hn : 0<n) :
    8 ∣ 2^n * (2*(a-1)+6) := by
  have h4 : 4 ∣ 2*(a-1)+6 := by
    refine ⟨a/2+1,?_⟩
    omega
  have h2 : 2 ∣ 2^n := by
    simpa using (Nat.pow_dvd_pow 2 (show 1≤n by omega) : (2:Nat)^1 ∣ (2:Nat)^n)
  rcases h4 with ⟨q,hq⟩
  rcases h2 with ⟨p,hp⟩
  refine ⟨p*q,?_⟩
  rw [hq,hp]
  simp only [show (8:Nat)=2*4 by decide]
  ac_rfl

/-- Uniform source law: if the output right coordinate is even at least six
    and output coordinate sum is 1 mod4, every predecessor is the direct one. -/
theorem only_direct_mod4_one (a k x y : Nat)
    (hy : 6≤y) (he : y%2=0) (hmod : (x+y)%4=1)
    (h : sectionPreimageAll a k x y) :
    a=x+y-2 ∧ 2*k+2=y := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at h
      all_goals (rcases h with ⟨hx, hy0⟩; omega)
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at h
        all_goals (rcases h with ⟨hx, hy0⟩; omega)
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at h
        obtain ⟨_,n,hs,_⟩ := h
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
        all_goals (rcases h with ⟨hx, hy0⟩; omega)
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at h
          all_goals (rcases h with ⟨hx, hy0⟩; omega)
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at h
            all_goals (rcases h with ⟨hx, hy0⟩; omega)
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at h
              all_goals (rcases h with ⟨hx, hy0⟩; omega)
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              rcases h with ⟨hy,_⟩ | ⟨_,n,hs,_⟩
              · omega
              · omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
        all_goals (rcases h with ⟨hx, hy0⟩; omega)
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
            if_neg hk0,if_pos hlow] at h
          omega
        · by_cases heven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos heven] at h
            obtain ⟨_,n,hs,_⟩ := h
            have hd := mul_even a n
            rw [←hs] at hd
            omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg heven] at h
            rcases h with ⟨hy,_⟩ | ⟨_,n,hs,_⟩
            · omega
            · have haodd : a%2=1 := by omega
              have hd := mul_four_odd a n haodd
              rw [←hs] at hd
              omega

/-- The sharp source-sector first predecessor is a direct corollary. -/
theorem first_parent_generic (s t a k : Nat)
    (h : sectionPreimageAll a k (8*s+1) (16*t+20)) :
    a=8*s+16*t+19 ∧ k=8*t+9 := by
  have hh := only_direct_mod4_one a k (8*s+1) (16*t+20)
    (by omega) (by omega) (by omega) h
  omega

/-- Every parent of that direct parent is a forbidden-image state. -/
theorem second_parent_generic (s t b l : Nat)
    (h : sectionPreimageAll b l (8*s+16*t+19) (8*t+9)) :
    b=4*s+12*t+12 ∧ l=2*s+10*t+9 := by
  by_cases hb0 : b=0
  · by_cases hl0 : l=0
    · simp [sectionPreimageAll,hb0,hl0] at h
    · by_cases hl1 : l=1
      · simp [sectionPreimageAll,hb0,hl0,hl1] at h
      · simp only [sectionPreimageAll,if_pos hb0,if_neg hl0,if_neg hl1] at h
        obtain ⟨_,n,hs,_⟩ := h
        omega
  · by_cases hb1 : b=1
    · by_cases hl0 : l=0
      · simp [sectionPreimageAll,hb0,hb1,hl0] at h
      · by_cases hl1 : l=1
        · simp [sectionPreimageAll,hb0,hb1,hl0,hl1] at h
        · by_cases hl2 : l=2
          · simp [sectionPreimageAll,hb0,hb1,hl0,hl1,hl2] at h
          · by_cases hl3 : l=3
            · simp [sectionPreimageAll,hb0,hb1,hl0,hl1,hl2,hl3] at h
            · simp only [sectionPreimageAll,if_neg hb0,if_pos hb1,
                if_neg hl0,if_neg hl1,if_neg hl2,if_neg hl3] at h
              rcases h with ⟨hy,_⟩ | ⟨_,n,hs,_⟩
              · omega
              · omega
    · by_cases hl0 : l=0
      · simp [sectionPreimageAll,hb0,hb1,hl0] at h
      · by_cases hlow : 2*l≤b
        · simp only [sectionPreimageAll,if_neg hb0,if_neg hb1,
            if_neg hl0,if_pos hlow] at h
          omega
        · by_cases heven : b%2=0
          · simp only [sectionPreimageAll,if_neg hb0,if_neg hb1,
              if_neg hl0,if_neg hlow,if_pos heven] at h
            obtain ⟨_,n,hs,hc⟩ := h
            have hn : n=0 := by
              by_cases hn0 : n=0
              · exact hn0
              · have hn1 : 0<n := by omega
                have hd := mul_eight_even b n heven (by omega) hn1
                rw [←hs] at hd
                omega
            subst n
            simp at hs hc
            omega
          · simp only [sectionPreimageAll,if_neg hb0,if_neg hb1,
              if_neg hl0,if_neg hlow,if_neg heven] at h
            rcases h with ⟨hy,_⟩ | ⟨_,n,hs,_⟩
            · omega
            · have hbodd : b%2=1 := by omega
              have hd := mul_four_odd b n hbodd
              rw [←hs] at hd
              omega

/-- The original first sector as a specialization of the strip. -/
theorem first_parent (s t a k : Nat)
    (h : sectionPreimageAll a k (16*s+9) (32*t+36)) :
    a=16*s+32*t+43 ∧ k=16*t+17 := by
  have he : 8*(2*s+1)+1=16*s+9 := by omega
  have hf : 16*(2*t+1)+20=32*t+36 := by omega
  have hh := first_parent_generic (2*s+1) (2*t+1) a k
    (by simpa only [he,hf] using h)
  omega

/-- The second predecessor specializes to the same sector. -/
theorem second_parent (s t b l : Nat)
    (h : sectionPreimageAll b l (16*s+32*t+43) (16*t+17)) :
    b=8*s+24*t+28 ∧ l=4*s+20*t+21 := by
  have he : 8*(2*s+1)+16*(2*t+1)+19=16*s+32*t+43 := by omega
  have hf : 8*(2*t+1)+9=16*t+17 := by omega
  have hh := second_parent_generic (2*s+1) (2*t+1) b l
    (by simpa only [he,hf] using h)
  omega

#print axioms only_direct_mod4_one
#print axioms first_parent_generic
#print axioms second_parent_generic
#print axioms first_parent
#print axioms second_parent
end BB6.Agent4Three

