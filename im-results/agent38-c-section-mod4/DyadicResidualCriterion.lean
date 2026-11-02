import DyadicDepthPrune
import BlankDyadicGate
import Lean.Elab.Tactic.Omega

namespace BB6Agent38
open BB6.Agent46

/-- The parity of an exact high-sector stopping level is determined by
    its recursion depth, for every starting middle counter. -/
theorem haltLevel_parity (k n : Nat) :
    (haltLevel k n+n)%2=1 := by
  induction n generalizing k with
  | zero => simp [haltLevel]
  | succ n ih =>
    have h := ih (2*k+4)
    change (2*k+5+haltLevel (2*k+4) n+(n+1))%2=1
    omega

/-- All authentic-blank reachable dyadic stopping inputs lie in the
    explicitly restricted depth/residue family. -/
theorem blank_section_residual (time a k : Nat)
    (hr : BB6.Agent8Section.run secNext time (some (5,1))=some (a,k))
    (ht : SectionHaltTarget a k) :
    (a=1 ∧ 4≤k ∧ ∃ n, 2*k-3=haltLevel 4 n ∧ n%8≠2) ∨
    (3≤a ∧ a%2=1 ∧ a<2*k ∧
      ∃ n, 2*k-a+3=haltLevel (a-1) n ∧ n%2=1 ∧ a%8≠(3*n)%8) := by
  rcases ht with ⟨ha,hk⟩ | ⟨ha,hk4,n,hlevel⟩ | ⟨ha,hao,hrange,n,hlevel⟩
  · have hpos := blank_section_positive time a k hr
    omega
  · left
    refine ⟨ha,hk4,n,hlevel,?_⟩
    intro hmod
    subst a
    exact dyadic_one_depth_two_mod8_excluded k n time hk4 hlevel hmod hr
  · right
    have hpar := haltLevel_parity (a-1) n
    have hnodd : n%2=1 := by omega
    refine ⟨ha,hao,hrange,n,hlevel,hnodd,?_⟩
    intro hmod
    exact dyadic_odd_depth_mod8_excluded a k n time ha hao hnodd hrange hlevel hmod hr

/-- Exact original blank-entry stopping criterion after eliminating whole
    depth/residue congruence sectors of Agent 46's dyadic halting basin. -/
theorem blank_halts_iff_mod8_residual :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k : Nat,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ 4≤k ∧ ∃ depth, 2*k-3=haltLevel 4 depth ∧ depth%8≠2) ∨
         (3≤a ∧ a%2=1 ∧ a<2*k ∧
           ∃ depth, 2*k-a+3=haltLevel (a-1) depth ∧ depth%2=1 ∧
             a%8≠(3*depth)%8)) := by
  rw [blank_halts_iff_reaches_dyadic_target]
  constructor
  · rintro ⟨time,a,k,hr,ht⟩
    exact ⟨time,a,k,hr,blank_section_residual time a k hr ht⟩
  · rintro ⟨time,a,k,hr,ht⟩
    refine ⟨time,a,k,hr,?_⟩
    rcases ht with ⟨ha,hk,depth,hlevel,_⟩ |
      ⟨ha,hao,hrange,depth,hlevel,_,_⟩
    · exact Or.inr (Or.inl ⟨ha,hk,depth,hlevel⟩)
    · exact Or.inr (Or.inr ⟨ha,hao,hrange,depth,hlevel⟩)

#print axioms haltLevel_parity
#print axioms blank_section_residual
#print axioms blank_halts_iff_mod8_residual

end BB6Agent38
