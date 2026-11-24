import HeightCone
import ModularConeFullCriterion
import FastFullBoolean
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 4000000

namespace BB6.Agent42ModularCone

def highTarget (j m : Nat) : Nat := 2^(2*m+2)*(j+3)-(j+3*m+5)
def highHeightExcluded (j m : Nat) : Bool := heightExcluded 32 (2*j+3) (highTarget j m)

def highAllowedHeight (j m : Nat) : Prop :=
  highAllowedFullModular j m ∧ highHeightExcluded j m=false

/-- Lossless extension of the accepted original-source Boolean/C70/modular
    stopping criterion. The new filter uses the actual target's height. -/
theorem blank_halts_iff_height :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedFullModular m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedHeight j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3) (highTarget j m)=true) := by
  rw [blank_halts_iff_full_modular]
  constructor
  · rintro (h | ⟨j,m,hallow,hroot⟩)
    · exact Or.inl h
    · have hreach : BB6.Agent3.CReach (2*j+3) (highTarget j m) :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      have hnew : highHeightExcluded j m=false := by
        cases hc : highHeightExcluded j m with
        | false => rfl
        | true =>
          exact False.elim ((source_height_excluded 32 (2*j+3) (highTarget j m) hc) hreach)
      exact Or.inr ⟨j,m,⟨hallow,hnew⟩,hroot⟩
  · rintro (h | ⟨j,m,hallow,hroot⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j,m,hallow.1,hroot⟩

/-- Diagnostic against the earlier full Boolean, C70 and modular guards.
    A nonempty result is a strictness witness for the parameter predicate,
    not a new decision of the source machine. -/
def priorSurvives (j m : Nat) : Bool :=
  BB6.Agent27FastBool.fastHighAllowedFullBool j m &&
  decide (¬((j%128=63 ∧ m%128=82) ∨ (j%128=127 ∧ m%128=18))) &&
  !highStopExcluded (j+1) m

def extraHeightExamples (limit : Nat) : List (Nat × Nat) :=
  ((List.range 6).flatMap fun m => (List.range limit).filterMap fun j =>
    if highHeightExcluded j m && priorSurvives j m then some (j,m) else none).take 16

set_option maxRecDepth 10000 in
#eval extraHeightExamples 256

#print axioms blank_halts_iff_height
end BB6.Agent42ModularCone
