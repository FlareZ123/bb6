import PowerDegreeExact
import UnboundedInDegree
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Complete classification of all arithmetic predecessors of every
    even zero-first section target, not restricted to powers of two.
    This is the NECESSARY half of the uniform exact source theorem. -/
theorem zero_even_parents_only (a k y : Nat) (hy : 16≤y)
    (he : y%2=0) (h : sectionPreimageAll a k 0 y) :
    (a=y-2 ∧ k=y/2-1) ∨
    (∃ r u : Nat, 2≤u ∧ y=8*4^r*u ∧ a=2*u-2 ∧ k=y-(u+4+3*r)) ∨
    (∃ r : Nat, y=16*4^r ∧ a=0 ∧ k=y-(3*r+6)) := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at h
        omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at h
        rcases h with ⟨_,n,hs,hc⟩
        have hn : n%2=1 := by omega
        let r : Nat := n/2
        have hrn : n=2*r+1 := by dsimp [r]; omega
        have hpow : 2^(2*r+1)=2*4^r := by
          rw [show 2*r+1=2*r+1 by omega,Nat.pow_succ,degree_two_pow_double]
          omega
        have hyEq : y=16*4^r := by
          rw [hrn,hpow] at hs
          omega
        right
        right
        exact ⟨r,hyEq,ha0,by omega⟩
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,if_neg hk0,
                if_neg hk1,if_neg hk2,if_neg hk3] at h
              rcases h with ⟨h3,_⟩ | ⟨_,n,hs,_⟩
              · omega
              · have hh : (y+1)%2=1 := by omega
                have hp : (2^n*16)%2=0 := by
                  have heq : 2^n*16=2*(2^n*8) := by omega
                  rw [heq]
                  omega
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
        omega
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_pos hlow] at h
          rcases h with ⟨hx,hy'⟩
          left
          constructor
          · omega
          · omega
        · by_cases haEven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,
              if_neg hlow,if_pos haEven] at h
            rcases h with ⟨_,n,hs,hc⟩
            have hcost : 2*k+a+7+3*n=2*y := by omega
            have hn : n%2=1 := degree_high_even_depth_odd a k n y haEven hcost
            let r : Nat := n/2
            let u : Nat := a/2+1
            have hrn : n=2*r+1 := by dsimp [r]; omega
            have hu : 2≤u := by dsimp [u]; omega
            have haeq : a=2*u-2 := by dsimp [u]; omega
            have hfactor : 2*(a-1)+6=4*u := by omega
            have hnum : 2^(2*r+1)=2*4^r := by
              rw [show 2*r+1=(2*r)+1 by omega,Nat.pow_succ,degree_two_pow_double]
              omega
            have hsum : y=8*4^r*u := by
              rw [hfactor,hrn,hnum] at hs
              calc
                y=2*4^r*(4*u) := by simpa only [Nat.zero_add] using hs
                _=8*4^r*u := by
                  calc
                    2*4^r*(4*u) = (2*4)*(4^r*u) := by ac_rfl
                    _=8*4^r*u := by simp [Nat.mul_assoc]
            right
            left
            refine ⟨r,u,hu,hsum,haeq,?_⟩
            omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,
              if_neg hlow,if_neg haEven] at h
            rcases h with ⟨h3,_⟩ | ⟨_,n,hs,_⟩
            · omega
            · have hh : (y+1)%2=1 := by omega
              have hp : (2^n*(2*(a-1)+8))%2=0 := by
                have eq : 2*(a-1)+8=2*((a-1)+4) := by omega
                rw [eq]
                have hex : 2^n*(2*((a-1)+4))=2*(2^n*((a-1)+4)) := by ac_rfl
                rw [hex]
                omega
              omega

/-- The direct low branch is a genuine original-source predecessor of any
    even zero-first target y>=16. -/
theorem direct_even_source_criterion (y : Nat)
    (hy : 16≤y) (he : y%2=0) :
    sectionPreimageAll (y-2) (y/2-1) 0 y := by
  let a : Nat := y-2
  let k : Nat := y/2-1
  have ha : a+2=y := by dsimp [a]; omega
  have hk : k+1=y/2 := by dsimp [k]; omega
  have hkY : 2*k+2=y := by omega
  have hreg : 2*k≤a := by omega
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  change sectionPreimageAll a k 0 y
  simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_pos hreg]
  exact ⟨by omega,hkY.symm⟩

/-- UNIVERSAL iff for the original Machine C section at EVERY even output
    (0,y), y>=16, with unrestricted bounce depth. The three disjoint source
    sectors are: direct, odd-bounce high-even (parameters r,u), and the rare
    dyadic exceptional first-zero source. Every witness is a real source
    transition, so this is an EXACT inverse relation. -/
theorem zero_even_preimages_iff (a k y : Nat)
    (hy : 16≤y) (he : y%2=0) :
    secNext (a,k)=some (0,y) ↔
    (a=y-2 ∧ k=y/2-1) ∨
    (∃ r u : Nat, 2≤u ∧ y=8*4^r*u ∧ a=2*u-2 ∧ k=y-(u+4+3*r)) ∨
    (∃ r : Nat, y=16*4^r ∧ a=0 ∧ k=y-(3*r+6)) := by
  constructor
  · intro h
    exact zero_even_parents_only a k y hy he
      ((section_preimage_all_iff a k 0 y).mp h)
  · rintro (⟨rfl,rfl⟩ | ⟨r,u,hu,hy',ha',hk'⟩ | ⟨r,hy',ha',hk'⟩)
    · exact (section_preimage_all_iff (y-2) (y/2-1) 0 y).mpr
        (direct_even_source_criterion y hy he)
    · subst y
      subst a
      subst k
      exact general_zero_even_parent r u hu
    · subst y
      subst a
      subst k
      exact (section_preimage_all_iff 0 (16*4^r-(3*r+6)) 0 (16*4^r)).mpr
        (zero_source_criterion r)

#print axioms zero_even_preimages_iff
#print axioms zero_even_parents_only
end BB6.Agent3
