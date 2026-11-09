import CThreeSixCriterion
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11SixAll

/-- The same exact unbounded six-sector inverse exclusion applies to
    the low stopping family. The high family already carries this
    recursive original-source filter through CThreeSixCriterion. -/
def lowAllowed (m : Nat) : Prop :=
  BB6.Agent11C58ValSix.lowAllowed m ∧
  BB6.Agent11SixForced.sixForcedExcluded 1
    (2^(2*m+3)-(3*m+4))=false

def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11SixCriterion.highAllowed j m

/-- Lossless Machine C genuine-blank halting criterion with six-sector
    recursive source filtering on BOTH low and high stopping branches,
    and with the new six-sector exact fixed-target decision on both sides.
    The parameter existentials are still unbounded: this is an effective
    narrowing and a faster fixed-target decision, not a global nonhalt. -/
theorem blank_halts_iff_six_both :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11SixCriterion.blank_halts_iff_six_forced]
  constructor
  · rintro (⟨m,hprior,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff 1 k).mp hroot
      have hf : BB6.Agent11SixForced.sixForcedExcluded 1 k=false := by
        cases h : BB6.Agent11SixForced.sixForcedExcluded 1 k with
        | false => rfl
        | true =>
            exact False.elim
              ((BB6.Agent11SixForced.sixForcedExcluded_sound 1 k h) hr)
      have hnew : BB6.Agent11SixForced.sixForcedRootDecision 1 k=true :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mpr hr
      exact Or.inl ⟨m,⟨hprior,hf⟩,hnew⟩
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hnew : BB6.Agent11SixForced.sixForcedRootDecision (2*j+3) k=true :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff (2*j+3) k).mpr hr
      exact Or.inr ⟨j,m,hprior,hnew⟩
  · rintro (⟨m,⟨hprior,_⟩,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mp hroot
      have hold : BB6.Agent3ValSix.valSixMixedRootDecision 1 k=true :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff 1 k).mpr hr
      exact Or.inl ⟨m,hprior,hold⟩
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff (2*j+3) k).mp hroot
      have hold : BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3) k=true :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mpr hr
      exact Or.inr ⟨j,m,hprior,hold⟩

/-- A low halting candidate rejected by the new recursive six-sector
    root filter. Its predecessor path uses the added valuation-two gate. -/
set_option maxRecDepth 8192 in
theorem low_three_excluded :
    BB6.Agent11SixForced.sixForcedExcluded 1
      (2^(2*3+3)-(3*3+4))=true := by
  decide

#print axioms blank_halts_iff_six_both
#print axioms low_three_excluded

end BB6.Agent11SixAll
