import StrongJointResidual
import ValSixC58AllDepthBool
import Lean.Elab.Tactic.Omega

namespace BB6.Agent27Phase

/-- Both exact source-certified exceptional-phase high gates. -/
def phaseGate (r j m : Nat) : Prop :=
  8 ≤ r ∧ r+4 ≤ 2*m+2 ∧
    ((j%16=(2*r)%16 ∧ (j+3*m+3)%2^(r+4)=9*2^r) ∨
     (j%16=(12+2*r)%16 ∧ (j+3*m+3)%2^(r+4)=13*2^r))

instance (r j m : Nat) : Decidable (phaseGate r j m) := by
  unfold phaseGate
  infer_instance

/-- Bounded finite search for the newer exclusion. Its range includes
    every r satisfying r+4 ≤ 2*m+2; no depth truncation is introduced. -/
def phaseExcludedBool (j m : Nat) : Bool :=
  (List.range (2*m+1)).any (fun r => decide (phaseGate r j m))

theorem phaseExcludedBool_iff (j m : Nat) :
    phaseExcludedBool j m = true ↔ BB6.Agent46.allPhaseExcluded j m := by
  simp only [phaseExcludedBool, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨r, _, hg⟩
    exact ⟨r, hg.1, hg.2.1, hg.2.2⟩
  · rintro ⟨r, hr8, hwidth, hcases⟩
    exact ⟨r, by omega, hr8, hwidth, hcases⟩

theorem phaseAllowedBool_iff (j m : Nat) :
    phaseExcludedBool j m = false ↔ ¬ BB6.Agent46.allPhaseExcluded j m := by
  rw [← phaseExcludedBool_iff]
  cases phaseExcludedBool j m <;> simp

/-- The full strongest source high predicate, with its two depth-indexed
    exclusions exposed as independently computable finite Booleans. The
    previously integrated algebraic guard remains a source-level Prop. -/
def highAllowedGuarded (j m : Nat) : Prop :=
  BB6.Agent11C58ValSix.highAllowed j m ∧
  BB6.Agent11GateDecision.allowedBool j m = true ∧
  phaseExcludedBool j m = false

theorem highAllowedGuarded_iff (j m : Nat) :
    highAllowedGuarded j m ↔ BB6.Agent24Phase.highAllowed j m := by
  unfold highAllowedGuarded BB6.Agent24Phase.highAllowed
    BB6.Agent11C58AllDepth.highAllowed
  constructor
  · rintro ⟨hprior,hdepth,hphase⟩
    exact ⟨⟨hprior, (BB6.Agent11GateDecision.allowedBool_iff j m).mp hdepth⟩,
      (phaseAllowedBool_iff j m).mp hphase⟩
  · rintro ⟨⟨hprior,hdepth⟩,hphase⟩
    exact ⟨hprior, (BB6.Agent11GateDecision.allowedBool_iff j m).mpr hdepth,
      (phaseAllowedBool_iff j m).mpr hphase⟩

/-- Lossless rewrite of the genuine blank-root halting iff: the new
    exceptional-phase infinite condition is decided by a bounded Boolean
    for each (j,m). Both parameter existentials remain unbounded. -/
theorem blank_halts_iff_joint_guarded :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
         BB6.Agent3ValSix.valSixMixedRootDecision 1
           (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedGuarded j m ∧
         BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
           (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent24Phase.blank_halts_iff_c58_two_sided_all_phase]
  constructor
  · rintro (hlow | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,(highAllowedGuarded_iff j m).mpr hallowed,hroot⟩
  · rintro (hlow | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,(highAllowedGuarded_iff j m).mp hallowed,hroot⟩

#print axioms phaseExcludedBool_iff
#print axioms phaseAllowedBool_iff
#print axioms highAllowedGuarded_iff
#print axioms blank_halts_iff_joint_guarded
end BB6.Agent27Phase
