import Lean.Elab.Tactic.Omega

namespace BB6.Agent11GateDecision

/-- Exact arithmetic condition for a source-certified dyadic-depth
    high stopping exclusion. -/
def gate (r j m : Nat) : Prop :=
  2≤r ∧ 3≤m ∧ r+4≤2*m+2 ∧
  m%4=(2*r+3)%4 ∧
  (j+9*m+14)%2^(r+4)=3*2^(r+2)

instance (r j m : Nat) : Decidable (gate r j m) := by
  unfold gate
  infer_instance

/-- Effective finite test, without a global root-search cutoff.
    The bound on r follows from the stopping equation itself. -/
def allowedBool (j m : Nat) : Bool :=
  (List.range (2*m+1)).all (fun r => decide (¬ gate r j m))

theorem allowedBool_iff (j m : Nat) :
    allowedBool j m = true ↔ ∀ r, ¬gate r j m := by
  simp only [allowedBool, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h r hg
    have hr : r<2*m+1 := by
      dsimp [gate] at hg
      omega
    exact h r hr hg
  · intro h r _
    exact h r

#print axioms allowedBool_iff
end BB6.Agent11GateDecision
