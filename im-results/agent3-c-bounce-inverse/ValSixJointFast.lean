import ValSixJointThree
import ValSixMixedNormalize

namespace BB6.Agent3ValSix

theorem blank_halts_iff_joint_val_six_fast :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent3.jointLowAllowed m ∧
        valSixMixedRootDecision 1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedValSixThree j m ∧
        valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  simpa only [BB6.Agent3.mixedFastRootDecision_iff,
    valSixMixedRootDecision_iff] using blank_halts_iff_joint_val_six_three

#print axioms blank_halts_iff_joint_val_six_fast
end BB6.Agent3ValSix
