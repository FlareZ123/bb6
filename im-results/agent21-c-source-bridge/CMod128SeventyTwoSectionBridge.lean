import CMod128SeventyTwo
import SectionReachEquivalence
import BlankParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

open BB6.Agent46

/-- The raw CLine reset at j=128*t+72 is exactly the high stopping
    family with section parameter J=128*t+71 and m=0. -/
theorem high_m0_128_71_unreachable (t : Nat) :
    ¬ CReach (2*(128*t+71)+3) (3*(128*t+71)+7) := by
  intro h
  have hline : BB6CLine.Reach
      (2*(128*t+71)+3, 3*(128*t+71)+7, 0) :=
    (cLine_c0_reach_iff_section_reach _ _).mp h
  have heq :
      (2*(128*t+71)+3, 3*(128*t+71)+7, 0) =
        (256*t+145, 384*t+220, 0) := by
    apply Prod.ext
    · omega
    · apply Prod.ext
      · simp [Nat.mul_add]
        rw [← Nat.mul_assoc]
      · rfl
  have hline' : BB6CLine.Reach (256*t+145, 384*t+220, 0) := by
    exact heq ▸ hline
  exact BB6.CMod128SeventyTwo.reset_mod128_seventytwo_unreachable t hline'

/-- The exact two-parametric-family blank-halting criterion can be
    sharpened by removing the high-stop m=0 residue J=71 mod 128.
    All m>=1 high witnesses are left unchanged. -/
theorem blank_halts_iff_two_parametric_families_with_m0_128_71_excluded :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run secNext time (some (5,1)) = some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3)) ∨
         (∃ j m, a=2*j+3 ∧
           k+j+3*m+5=2^(2*m+2)*(j+3) ∧
           (m≠0 ∨ j%128≠71))) := by
  constructor
  · intro hRun
    rcases (blank_halts_iff_two_parametric_families).mp hRun with
      ⟨time,a,k,hr,hfamily⟩
    refine ⟨time,a,k,hr,?_⟩
    rcases hfamily with hlow | ⟨j,m,ha,heq⟩
    · exact Or.inl hlow
    · by_cases hm : m=0
      · subst m
        have hj : j%128≠71 := by
          intro hmod
          have hdiv : j=128*(j/128)+71 := by omega
          let t := j/128
          have hdiv' : j=128*t+71 := by simpa [t] using hdiv
          have ha' : a=2*(128*t+71)+3 := by omega
          have heq0 : k+j+5=4*(j+3) := by simpa using heq
          have hk' : k=3*(128*t+71)+7 := by omega
          have hreach : CReach a k := ⟨time,hr⟩
          have hroot :
              CReach (2*(128*t+71)+3) (3*(128*t+71)+7) := by
            simpa [ha',hk'] using hreach
          exact high_m0_128_71_unreachable t hroot
        exact Or.inr ⟨j,0,ha,heq,Or.inr hj⟩
      · exact Or.inr ⟨j,m,ha,heq,Or.inl hm⟩
  · intro hNew
    rcases hNew with ⟨time,a,k,hr,hfamily⟩
    apply (blank_halts_iff_two_parametric_families).mpr
    refine ⟨time,a,k,hr,?_⟩
    rcases hfamily with hlow | ⟨j,m,ha,heq,hgate⟩
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,ha,heq⟩

#print axioms high_m0_128_71_unreachable
#print axioms blank_halts_iff_two_parametric_families_with_m0_128_71_excluded

end BB6.Agent15
