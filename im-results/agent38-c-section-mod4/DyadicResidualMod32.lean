import ThirdStageOddDepth
import Lean.Elab.Tactic.Omega

namespace BB6Agent38
open BB6.Agent46

/-- Third independent, globally quantified stopping-depth obstruction:
    the full, true blank-origin C machine can stop only in the
    explicitly residual arithmetic families with the third level
    of odd-depth congruence obstructions removed. -/
theorem blank_halts_iff_mod32_residual :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k : Nat,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ 4≤k ∧
            ∃ depth, 2*k-3=haltLevel 4 depth ∧ depth%8≠2 ∧ depth%16≠8) ∨
         (3≤a ∧ a%2=1 ∧ a<2*k ∧
            ∃ depth, 2*k-a+3=haltLevel (a-1) depth ∧ depth%2=1 ∧
              a%8≠(3*depth)%8 ∧
              (a%4≠1 ∨ (a+3*depth+4)%16≠0) ∧
              (depth<3 ∨ a%4≠3 ∨ (a+depth)%32≠16))) := by
  rw [blank_halts_iff_mod16_residual]
  constructor
  · rintro ⟨time,a,k,hr,ht⟩
    refine ⟨time,a,k,hr,?_⟩
    rcases ht with h1 | ⟨ha,hao,hrange,depth,hlevel,hodd,h8,h16⟩
    · exact Or.inl h1
    · right
      refine ⟨ha,hao,hrange,depth,hlevel,hodd,h8,h16,?_⟩
      by_cases hsmall : depth<3
      · exact Or.inl hsmall
      · right
        by_cases h4 : a%4=3
        · right
          intro hsum
          exact dyadic_odd_depth_four_mod16_classes a k depth time
            ha hao (by omega) hrange hlevel h4 hsum hr
        · exact Or.inl h4
  · rintro ⟨time,a,k,hr,ht⟩
    refine ⟨time,a,k,hr,?_⟩
    rcases ht with h1 |
      ⟨ha,hao,hrange,depth,hlevel,hodd,h8,h16,_⟩
    · exact Or.inl h1
    · exact Or.inr ⟨ha,hao,hrange,depth,hlevel,hodd,h8,h16⟩

#print axioms blank_halts_iff_mod32_residual
end BB6Agent38
