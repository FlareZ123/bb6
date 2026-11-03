import OddSliver
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem even_child_depth_zero (x y n b : Nat)
    (hs : (x+y)%8=3) (hb : 4 ∣ b)
    (h : x+y+1=2^n*b) : n=0 := by
  cases n with
  | zero => rfl
  | succ n =>
      have htwo : 2 ∣ 2^(n+1) := by
        change 2^1 ∣ 2^(n+1)
        exact Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨u,hu⟩ := htwo
      obtain ⟨v,hv⟩ := hb
      have hd : 8 ∣ x+y+1 := by
        refine ⟨u*v,?_⟩
        calc
          x+y+1 = 2^(n+1)*b := h
          _ = (2*u)*(4*v) := by rw [hu,hv]
          _ = 8*(u*v) := by ac_rfl
      omega

/-- Full source iff for every output with even y >=4 and
    odd sum x+y=3 mod8. Only the direct low source can produce it. -/
theorem even_child_parent_iff (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=0) (hy4 : 4≤y)
    (hs : (x+y)%8=3) :
    secNext (a,k)=some (x,y) ↔
      a=x+y-2 ∧ k=y/2-1 := by
  constructor
  · intro h
    have hp := (section_preimage_all_iff a k x y).mp h
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,hk0] at hp
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
          omega
        · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at hp
          obtain ⟨_,n,heq,_⟩ := hp
          have hd : 2 ∣ 2^n*8 := ⟨2^n*4,by omega⟩
          omega
    · by_cases ha1 : a=1
      · by_cases hk0 : k=0
        · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
          omega
        · by_cases hk1 : k=1
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp
            omega
          · by_cases hk2 : k=2
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp
              omega
            · by_cases hk3 : k=3
              · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp
                omega
              · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
                rcases hp with ⟨hy3,_⟩ | ⟨_,n,heq,_⟩
                · omega
                · have hd : 8 ∣ 2^n*16 := ⟨2^n*2,by omega⟩
                  omega
      · by_cases hk0 : k=0
        · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
          omega
        · by_cases hlow : 2*k≤a
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_pos hlow] at hp
            rcases hp with ⟨hxEq,hyEq⟩
            omega
          · by_cases heven : a%2=0
            · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
                if_neg hk0,if_neg hlow,if_pos heven] at hp
              obtain ⟨_,n,heq,_⟩ := hp
              have hd : 2 ∣ 2^n*(2*(a-1)+6) := by
                refine ⟨2^n*((a-1)+3),?_⟩
                calc
                  2^n*(2*(a-1)+6)=2^n*(2*((a-1)+3)) := by congr 1 <;> omega
                  _=2*(2^n*((a-1)+3)) := by ac_rfl
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
                if_neg hk0,if_neg hlow,if_neg heven] at hp
              rcases hp with ⟨hy3,_⟩ | ⟨_,n,heq,hcost⟩
              · omega
              · have hb : 4 ∣ 2*(a-1)+8 := by
                  refine ⟨(a-1)/2+2,?_⟩
                  omega
                have hn := even_child_depth_zero x y n _ hs hb heq
                subst n
                simp at heq hcost
                omega
  · rintro ⟨ha,hk⟩
    have hyEven : y=2*(y/2) := by omega
    have ha2 : 2≤a := by omega
    have hk1 : 1≤k := by omega
    have hlow : 2*k≤a := by omega
    apply (section_preimage_all_iff a k x y).mpr
    have hna0 : a≠0 := by omega
    have hna1 : a≠1 := by omega
    have hnk0 : k≠0 := by omega
    simp only [sectionPreimageAll,if_neg hna0,if_neg hna1,if_neg hnk0,if_pos hlow]
    omega

/-- Every point of the first even-child rectangle has as its only source
    a genuinely blank-forbidden point of the established odd wedge. -/
theorem even_child_A_unreachable (p q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (16*p+3,32*q+16) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some s =>
          rcases s with ⟨a,k⟩
          have ht : secNext (a,k)=some (16*p+3,32*q+16) := by
            simpa [BB6.Agent8Section.run,hp] using h
          obtain ⟨ha,hk⟩ := (even_child_parent_iff a k (16*p+3) (32*q+16)
            (by omega) (by omega) (by omega) (by omega)).mp ht
          have he : BB6.Agent8Section.run secNext n (some (5,1))=
              some (16*p+32*q+17,16*q+7) := by
            rw [ha,hk] at hp
            have h1 : 16*p+3+(32*q+16)-2=16*p+32*q+17 := by omega
            have h2 : (32*q+16)/2-1=16*q+7 := by omega
            rwa [h1,h2] at hp
          exact odd_sliver_blank_unreachable (16*p+32*q+17) (16*q+7) n
            (by omega) (by omega) (by omega) (by omega) (by omega) he

/-- The second even-child rectangle is also all-time unreachable. -/
theorem even_child_B_unreachable (p q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (16*p+11,32*q+32) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some s =>
          rcases s with ⟨a,k⟩
          have ht : secNext (a,k)=some (16*p+11,32*q+32) := by
            simpa [BB6.Agent8Section.run,hp] using h
          obtain ⟨ha,hk⟩ := (even_child_parent_iff a k (16*p+11) (32*q+32)
            (by omega) (by omega) (by omega) (by omega)).mp ht
          have he : BB6.Agent8Section.run secNext n (some (5,1))=
              some (16*p+32*q+41,16*q+15) := by
            rw [ha,hk] at hp
            have h1 : 16*p+11+(32*q+32)-2=16*p+32*q+41 := by omega
            have h2 : (32*q+32)/2-1=16*q+15 := by omega
            rwa [h1,h2] at hp
          exact odd_sliver_blank_unreachable (16*p+32*q+41) (16*q+15) n
            (by omega) (by omega) (by omega) (by omega) (by omega) he

#print axioms even_child_parent_iff
#print axioms even_child_A_unreachable
#print axioms even_child_B_unreachable
end BB6.Agent3
