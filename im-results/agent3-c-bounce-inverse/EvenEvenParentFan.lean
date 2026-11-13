import SectionAllInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ParentFan
open BB6.Agent46

/--
Complete source-parent fan for an even/even target with right coordinate at
least six. Unlike the sum-zero specialization, this theorem retains every
even-a bounce depth and the exceptional zero-left branch. The three
alternatives are exactly the surviving cases of sectionPreimageAll:
direct/low, a=0, or even-a bounce with odd depth n.
-/
theorem even_even_parent_fan (a k x y : Nat)
    (hxpos : 0<x) (hxe : x%2=0)
    (hy6 : 6≤y) (hye : y%2=0)
    (hedge : secNext (a,k)=some (x,y)) :
    (a=x+y-2 ∧ k=(y-2)/2) ∨
    (a=0 ∧ 2≤k ∧
      ∃ n : Nat, x+y=2^n*8 ∧ 2*k+9+3*n=x+2*y) ∨
    (2≤a ∧ a%2=0 ∧ 0<k ∧ a<2*k ∧
      ∃ n : Nat, n%2=1 ∧
        x+y=2^(n+1)*(a+2) ∧ 2*k+a+7+3*n=x+2*y) := by
  have hp := (section_preimage_all_iff a k x y).mp hedge
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
        omega
      · have hcase : 4≤y ∧ ∃ n : Nat,
            x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y := by
          simpa [sectionPreimageAll,ha0,hk0,hk1] using hp
        rcases hcase with ⟨_,n,hxy,hcost⟩
        right
        left
        exact ⟨ha0, by omega, ⟨n,hxy,by omega⟩⟩
  · by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,hk0] at hp <;> omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,hk0,hk1] at hp <;> omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,hk0,hk1,hk2] at hp <;> omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,hk0,hk1,hk2,hk3] at hp <;> omega
            · have hcase :
                  (y=3 ∧ ∃ n : Nat, x+6=2^n*16 ∧
                    (2*k-3)+16+3*n=x+10) ∨
                  (5≤y ∧ ∃ n : Nat, x+y+1=2^n*16 ∧
                    (2*k-3)+16+3*n=x+2*y+2) := by
                simpa [sectionPreimageAll,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hodd,_⟩
              · omega
              · have hoddxy : (x+y+1)%2=1 := by omega
                have hprod : (2^n*16)%2=0 := by simp [Nat.mul_mod]
                rw [hodd] at hoddxy
                rw [hprod] at hoddxy
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hlow : 2*k≤a
        · have hcase : x=a-2*k ∧ y=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          rcases hcase with ⟨hxx,hyy⟩
          left
          constructor <;> omega
        · by_cases haeven : a%2=0
          · have hcase : 4≤y ∧ ∃ n : Nat,
                x+y=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨_,n,hxy,hcost⟩
            have hnodd : n%2=1 := by omega
            have hfac : 2*(a-1)+6=2*(a+2) := by omega
            have hpow :
                2^n*(2*(a-1)+6)=2^(n+1)*(a+2) := by
              rw [hfac,Nat.pow_succ]
              exact (Nat.mul_assoc _ _ _).symm
            have hxy' : x+y=2^(n+1)*(a+2) := by
              rw [←hpow]
              exact hxy
            have hcost' : 2*k+a+7+3*n=x+2*y := by omega
            right
            right
            exact ⟨ha2,haeven,by omega,by omega,n,hnodd,hxy',hcost'⟩
          · have hcase :
                (y=3 ∧ ∃ n : Nat, x+6=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
                (5≤y ∧ ∃ n : Nat,
                  x+y+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hodd,_⟩
            · omega
            · have hoddxy : (x+y+1)%2=1 := by omega
              have hfac : (2*(a-1)+8)%2=0 := by omega
              have hprod :
                  (2^n*(2*(a-1)+8))%2=0 := by
                simp [Nat.mul_mod,hfac]
              rw [hodd] at hoddxy
              rw [hprod] at hoddxy
              omega

#print axioms even_even_parent_fan
end BB6.Agent3ParentFan
