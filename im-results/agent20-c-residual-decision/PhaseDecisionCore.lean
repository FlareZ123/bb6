import Lean.Elab.Tactic.Omega

namespace BB6.Agent20PhaseDecision

/-- The two exact source-excluded exceptional dyadic parameter patterns. -/
def phaseGate (r j m : Nat) : Prop :=
  8 ≤ r ∧ r + 4 ≤ 2*m + 2 ∧
  ((j % 16 = (2*r) % 16 ∧ (j+3*m+3) % 2^(r+4) = 9*2^r) ∨
   (j % 16 = (12+2*r) % 16 ∧ (j+3*m+3) % 2^(r+4) = 13*2^r))

instance (r j m : Nat) : Decidable (phaseGate r j m) := by
  unfold phaseGate
  infer_instance

/-- Exact Boolean phase test: true iff no forbidden inverse depth exists. -/
def phaseAllowedBool (j m : Nat) : Bool :=
  (List.range (2*m+1)).all (fun r => decide (¬ phaseGate r j m))

theorem phaseAllowedBool_iff (j m : Nat) :
    phaseAllowedBool j m = true ↔ ∀ r, ¬ phaseGate r j m := by
  simp only [phaseAllowedBool, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h r hg
    have hr : r < 2*m+1 := by
      dsimp [phaseGate] at hg
      omega
    exact h r hr hg
  · intro h r _
    exact h r

theorem phaseAllowedBool_iff_no_witness (j m : Nat) :
    phaseAllowedBool j m = true ↔ ¬ ∃ r, phaseGate r j m := by
  rw [phaseAllowedBool_iff]
  constructor
  · intro h ⟨r,hr⟩
    exact h r hr
  · intro h r hr
    exact h ⟨r,hr⟩

#print axioms phaseAllowedBool_iff
#print axioms phaseAllowedBool_iff_no_witness
end BB6.Agent20PhaseDecision
