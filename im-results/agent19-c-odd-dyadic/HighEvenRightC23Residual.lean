import C23Integration
import HighEvenRightResidual
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19HighEvenRight

/-- The new even-right cylinder also survives the later C70 high
    rectangles, since m is odd whereas both excluded right residues
    are even. -/
theorem high_even_right_family_prior_allowed_C70 (j m : Nat)
    (hm : 3≤m) (hm4 : m%4=3)
    (hj8 : j%8=(m+3)%8) :
    BB6.Agent20C70.highAllowedC70 j m := by
  refine ⟨high_even_right_family_prior_allowed j m hm hm4 hj8,?_⟩
  rintro ⟨⟨_,hm82⟩|⟨_,hm18⟩⟩
  · omega
  · omega

/-- The C23 high cylinder is disjoint from the new even-right cylinder:
    its congruence forces m=1 (mod 4), while the new family has m=3. -/
theorem high_even_right_family_prior_allowed_C23 (j m : Nat)
    (hm : 3≤m) (hm4 : m%4=3)
    (hj8 : j%8=(m+3)%8) :
    BB6.Agent20C23.highAllowedC23 j m := by
  have hC70 := high_even_right_family_prior_allowed_C70 j m hm hm4 hj8
  have hnotC23 : ¬(2≤m ∧ j%4=0 ∧ (j+7)%32=(3*m)%32) := by
    rintro ⟨_,hj4,hpair⟩
    omega
  exact ⟨hC70,hnotC23⟩

/-- The even-right source obstruction is strictly new relative to the
    strongest integrated C70+C23 high predicate. -/
theorem genuinely_new_high_even_right (j m : Nat)
    (hm : 3≤m) (hm4 : m%4=3)
    (hj8 : j%8=(m+3)%8) :
    BB6.Agent20C23.highAllowedC23 j m ∧
    ¬(BB6.Agent20C23.highAllowedC23 j m ∧
      ¬(3≤m ∧ m%4=3 ∧ j%8=(m+3)%8)) := by
  refine ⟨high_even_right_family_prior_allowed_C23 j m hm hm4 hj8,?_⟩
  intro h
  exact h.2 ⟨hm,hm4,hj8⟩

/-- Exact two-sided halting criterion obtained by adjoining the new
    even-right cylinder to Agent20's strongest C70+C23 residual. -/
def highAllowedC23WithEvenRight (j m : Nat) : Prop :=
  BB6.Agent20C23.highAllowedC23 j m ∧
  ¬(3≤m ∧ m%4=3 ∧ j%8=(m+3)%8)

theorem blank_halts_iff_c23_and_even_right :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent20C70.lowAllowedC70 m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedC23WithEvenRight j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent20C23.blank_halts_iff_c23]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · have hreach : BB6.Agent3.CReach (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5)) :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      have hnot : ¬(3≤m ∧ m%4=3 ∧ j%8=(m+3)%8) := by
        rintro ⟨hm,hm4,hj8⟩
        exact high_even_right_blank_unreachable j m hm hm4 hj8 hreach
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms high_even_right_family_prior_allowed_C70
#print axioms high_even_right_family_prior_allowed_C23
#print axioms genuinely_new_high_even_right
#print axioms blank_halts_iff_c23_and_even_right
end BB6.Agent19HighEvenRight
