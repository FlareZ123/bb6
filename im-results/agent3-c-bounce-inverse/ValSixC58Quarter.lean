import ValSixC58
import StrongMassQuarter

namespace BB6.Agent3StrongMass

private theorem merged_and_quarter_roots_equivalent (x y : Nat) :
    BB6.Agent3ValSix.valSixMixedRootDecision x y = true ↔
      quarterFuelRootDecision x y = true := by
  rw [BB6.Agent3ValSix.valSixMixedRootDecision_iff, quarterFuelRootDecision_iff]
  rfl

/-- Preserve all source-authentic ValSixFull and C58 low/high stopping restrictions
while using an exact backward root search bounded by one-quarter target mass. -/
theorem blank_halts_iff_val_six_c58_quarter :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        quarterFuelRootDecision 1 (2^(2*m+3)-(3*m+4)) = true) ∨
      (∃ j m, BB6.Agent11C58ValSix.highAllowed j m ∧
        quarterFuelRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5)) = true) := by
  rw [BB6.Agent11C58ValSix.blank_halts_iff_joint_val_six_c58]
  constructor
  · rintro (⟨m,hm,hroot⟩ | ⟨j,m,hm,hroot⟩)
    · exact Or.inl ⟨m,hm,
        (merged_and_quarter_roots_equivalent 1
          (2^(2*m+3)-(3*m+4))).mp hroot⟩
    · exact Or.inr ⟨j,m,hm,
        (merged_and_quarter_roots_equivalent (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))).mp hroot⟩
  · rintro (⟨m,hm,hroot⟩ | ⟨j,m,hm,hroot⟩)
    · exact Or.inl ⟨m,hm,
        (merged_and_quarter_roots_equivalent 1
          (2^(2*m+3)-(3*m+4))).mpr hroot⟩
    · exact Or.inr ⟨j,m,hm,
        (merged_and_quarter_roots_equivalent (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))).mpr hroot⟩

#print axioms blank_halts_iff_val_six_c58_quarter
end BB6.Agent3StrongMass
