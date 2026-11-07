import StrongJointResidual
import HighDyadicGateDecision
import PhaseDecisionCore

namespace BB6.Agent20PhaseDecision

/-- The finite evaluator is definitionally equivalent to Agent46's
    actual original-source all-depth exceptional-phase exclusion. -/
theorem phaseAllowedBool_iff_source (j m : Nat) :
    phaseAllowedBool j m = true ↔ ¬ BB6.Agent46.allPhaseExcluded j m := by
  simpa only [BB6.Agent46.allPhaseExcluded, phaseGate] using
    phaseAllowedBool_iff_no_witness j m

/-- This replaces both unbounded-depth quantifiers of the latest
    C58-plus-exceptional-phase sieve with Boolean finite tests.
    Earlier ValSix predicates remain as source propositions. -/
def highAllowedFiltered (j m : Nat) : Prop :=
  BB6.Agent11C58ValSix.highAllowed j m ∧
  BB6.Agent11GateDecision.allowedBool j m = true ∧
  phaseAllowedBool j m = true

theorem highAllowedFiltered_iff (j m : Nat) :
    highAllowedFiltered j m ↔ BB6.Agent24Phase.highAllowed j m := by
  unfold highAllowedFiltered BB6.Agent24Phase.highAllowed
    BB6.Agent11C58AllDepth.highAllowed
  constructor
  · rintro ⟨hprior,hbool,hphase⟩
    exact ⟨⟨hprior,(BB6.Agent11GateDecision.allowedBool_iff j m).mp hbool⟩,
      (phaseAllowedBool_iff_source j m).mp hphase⟩
  · rintro ⟨⟨hprior,hdepth⟩,hphase⟩
    exact ⟨hprior,(BB6.Agent11GateDecision.allowedBool_iff j m).mpr hdepth,
      (phaseAllowedBool_iff_source j m).mpr hphase⟩

/-- The source-connected all-phase halting equivalence restated with
    bounded, executable high-depth tests. The high ValSix predicate
    and both parameter existentials remain separate proof obligations. -/
theorem blank_halts_iff_filtered :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedFiltered j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent24Phase.blank_halts_iff_c58_two_sided_all_phase]
  constructor
  · rintro (hlow | ⟨j,m,hhigh,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,(highAllowedFiltered_iff j m).mpr hhigh,hroot⟩
  · rintro (hlow | ⟨j,m,hhigh,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,(highAllowedFiltered_iff j m).mp hhigh,hroot⟩

#print axioms phaseAllowedBool_iff_source
#print axioms highAllowedFiltered_iff
#print axioms blank_halts_iff_filtered
end BB6.Agent20PhaseDecision
