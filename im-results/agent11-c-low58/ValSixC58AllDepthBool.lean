import HighDyadicGateDecision
import ValSixC58AllDepth

namespace BB6.Agent11C58Boolean

def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11C58ValSix.highAllowed j m ∧
  BB6.Agent11GateDecision.allowedBool j m = true

theorem highAllowed_iff (j m : Nat) :
    highAllowed j m ↔ BB6.Agent11C58AllDepth.highAllowed j m := by
  unfold highAllowed BB6.Agent11C58AllDepth.highAllowed
  constructor
  · rintro ⟨hprior,hbool⟩
    exact ⟨hprior,(BB6.Agent11GateDecision.allowedBool_iff j m).mp hbool⟩
  · rintro ⟨hprior,hall⟩
    exact ⟨hprior,(BB6.Agent11GateDecision.allowedBool_iff j m).mpr hall⟩

/-- The all-depth original-source exact blank-halting equivalence,
    with an executable finite high-parameter gate. This still retains
    unbounded stopping parameters and does not solve Machine C. -/
theorem blank_halts_iff_c58_all_depth_boolean :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11C58AllDepth.blank_halts_iff_joint_c58_all_depth]
  constructor
  · rintro (hlow | ⟨j,m,hallow,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,(highAllowed_iff j m).mpr hallow,hroot⟩
  · rintro (hlow | ⟨j,m,hallow,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,(highAllowed_iff j m).mp hallow,hroot⟩

#print axioms highAllowed_iff
#print axioms blank_halts_iff_c58_all_depth_boolean
end BB6.Agent11C58Boolean
