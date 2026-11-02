import FourthStage
import Lean.Elab.Tactic.Omega

namespace BB6Agent38
open BB6.Agent46

/-- Genuine blank-entry Machine C stopping iff the shrinking arithmetic
    dyadic basin remains occupied after four independent global restrictions. -/
theorem blank_halts_iff_four_stage_residual :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k : Nat,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ 4≤k ∧
            ∃ depth, 2*k-3=haltLevel 4 depth ∧ depth%8≠2 ∧ depth%16≠8) ∨
         (3≤a ∧ a%2=1 ∧ a<2*k ∧
            ∃ depth, 2*k-a+3=haltLevel (a-1) depth ∧ depth%2=1 ∧
              a%8≠(3*depth)%8 ∧
              (a%4≠1 ∨ (a+3*depth+4)%16≠0) ∧
              (depth<3 ∨ a%4≠3 ∨ (a+depth)%32≠16) ∧
              (depth<3 ∨ a%8≠7 ∨ (a+3*depth)%16≠4))) := by
  rw [blank_halts_iff_mod32_residual]
  constructor
  · rintro ⟨time,a,k,hr,ht⟩
    refine ⟨time,a,k,hr,?_⟩
    rcases ht with h1 |
      ⟨ha,hao,hrange,depth,hlevel,hodd,h8,h16,h32⟩
    · exact Or.inl h1
    · right
      refine ⟨ha,hao,hrange,depth,hlevel,hodd,h8,h16,h32,?_⟩
      by_cases hsmall : depth<3
      · exact Or.inl hsmall
      · right
        by_cases ha7 : a%8=7
        · right
          intro htarget
          exact dyadic_odd_seven_four_excluded a k depth time ha hao
            (by omega) hrange hlevel ha7 htarget hr
        · exact Or.inl ha7
  · rintro ⟨time,a,k,hr,ht⟩
    refine ⟨time,a,k,hr,?_⟩
    rcases ht with h1 |
      ⟨ha,hao,hrange,depth,hlevel,hodd,h8,h16,h32,_⟩
    · exact Or.inl h1
    · exact Or.inr ⟨ha,hao,hrange,depth,hlevel,hodd,h8,h16,h32⟩

#print axioms blank_halts_iff_four_stage_residual
end BB6Agent38
