import ZeroOddForward
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Necessary universal inverse grammar for EVERY odd zero-first original
    section target. There are exactly three source types: the lone y=7
    exceptional, a dyadic a=1 source, and an all-depth two-parameter
    odd-first high source. -/
theorem zero_odd_parents_only (a k y : Nat) (ho : y%2=1)
    (h : sectionPreimageAll a k 0 y) :
    (y=7 ∧ a=1 ∧ k=3) ∨
    (∃ r : Nat, y=32*4^r-1 ∧ a=1 ∧ k=32*4^r-(8+3*r)) ∨
    (∃ r u : Nat, 1≤u ∧ y=4*4^r*(u+2)-1 ∧
        a=2*u+1 ∧ k=y-(u+4+3*r)) := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at h
        omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at h
        rcases h with ⟨_,n,hs,_⟩
        have heq : 2^n*8=2*(2^n*4) := by ac_rfl
        rw [heq] at hs
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at h
              rcases h with ⟨_,hy⟩
              exact Or.inl ⟨hy,ha1,hk3⟩
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              rcases h with ⟨_,n,hs,_⟩ | ⟨_,n,hs,hc⟩
              · have hp : 1≤2^n := Nat.one_le_pow n 2 (by decide)
                have hb : 16≤2^n*16 := by
                  calc
                    16≤16*2^n := Nat.le_mul_of_pos_right 16 hp
                    _=2^n*16 := by ac_rfl
                omega
              · have hnodd : n%2=1 := by omega
                let r : Nat := n/2
                have hn : n=2*r+1 := by dsimp [r]; omega
                have hp : 2^(2*r+1)*16=32*4^r := by
                  rw [show 2*r+1=(2*r)+1 by omega,Nat.pow_succ,degree_two_pow_double]
                  omega
                have hy : y=32*4^r-1 := by
                  rw [hn,hp] at hs
                  omega
                have hk : k=32*4^r-(8+3*r) := by omega
                exact Or.inr (Or.inl ⟨r,hy,ha1,hk⟩)
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
        omega
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_pos hlow] at h
          rcases h with ⟨_,hy⟩
          omega
        · by_cases haeven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos haeven] at h
            rcases h with ⟨_,n,hs,_⟩
            have heq : 2^n*(2*(a-1)+6)=2*(2^n*((a-1)+3)) := by
              calc
                2^n*(2*(a-1)+6)=
                  2^n*(2*((a-1)+3)) := by congr 1 <;> omega
                _=2*(2^n*((a-1)+3)) := by ac_rfl
            rw [heq] at hs
            omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at h
            rcases h with ⟨_,n,hs,_⟩ | ⟨_,n,hs,hc⟩
            · have hp : 1≤2^n := Nat.one_le_pow n 2 (by decide)
              have hb : 2*(a-1)+8≤2^n*(2*(a-1)+8) := by
                calc
                  2*(a-1)+8 ≤ (2*(a-1)+8)*2^n :=
                    Nat.le_mul_of_pos_right _ hp
                  _ = 2^n*(2*(a-1)+8) := by ac_rfl
              omega
            · have hneven : n%2=0 := by omega
              let r : Nat := n/2
              let u : Nat := (a-1)/2
              have hn : n=2*r := by dsimp [r]; omega
              have hu : 1≤u := by dsimp [u]; omega
              have ha : a=2*u+1 := by dsimp [u]; omega
              have hf : 2*(a-1)+8=4*(u+2) := by omega
              have hY : y+1=4*4^r*(u+2) := by
                rw [hn,degree_two_pow_double,hf] at hs
                calc
                  y+1=4^r*(4*(u+2)) := by simpa using hs
                  _=4*4^r*(u+2) := by ac_rfl
              have he : y=4*4^r*(u+2)-1 := by omega
              have hk : k=y-(u+4+3*r) := by omega
              exact Or.inr (Or.inr ⟨r,u,hu,he,ha,hk⟩)

/-- Exhaustive exact original-source iff for ALL odd zero-first outputs.
    Every arithmetic ancestor is a real unbounded-depth recursive edge. -/
theorem zero_odd_preimages_iff (a k y : Nat) (ho : y%2=1) :
    secNext (a,k)=some (0,y) ↔
    (y=7 ∧ a=1 ∧ k=3) ∨
    (∃ r : Nat, y=32*4^r-1 ∧ a=1 ∧ k=32*4^r-(8+3*r)) ∨
    (∃ r u : Nat, 1≤u ∧ y=4*4^r*(u+2)-1 ∧
        a=2*u+1 ∧ k=y-(u+4+3*r)) := by
  constructor
  · intro h
    exact zero_odd_parents_only a k y ho
      ((section_preimage_all_iff a k 0 y).mp h)
  · rintro (⟨hy,ha,hk⟩ | ⟨r,hy,ha,hk⟩ | ⟨r,u,hu,hy,ha,hk⟩)
    · subst y
      subst a
      subst k
      decide
    · subst y
      subst a
      subst k
      exact odd_one_source r
    · subst y
      subst a
      subst k
      exact odd_high_source r u hu

#print axioms zero_odd_preimages_iff
#print axioms zero_odd_parents_only
end BB6.Agent3
