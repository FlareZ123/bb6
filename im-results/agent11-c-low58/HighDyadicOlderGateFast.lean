import Lean
import Lean.Elab.Tactic.Omega
import HighDyadicGateDecisionFast

namespace BB6.Agent11OlderGateFast

open BB6.Agent11FastDepthGate

/-- Exact Agent19 parity-dependent inverse-depth guard. -/
def gate (n j m : Nat) : Prop :=
  n+4≤2*m+2 ∧
  (j+3*m+3)%2^(n+4)=2^(n+2) ∧
  (2*j+3)%8=(if n%2=0 then 7 else 3)

instance (n j m : Nat) : Decidable (gate n j m) := by
  unfold gate
  infer_instance

/-- The residue has odd quotient and therefore fixes the depth. -/
theorem v2_of_older_residue (j m n : Nat)
    (h : (j+3*m+3)%2^(n+4)=2^(n+2)) :
    v2 (j+3*m+3)=n+2 := by
  let D := j+3*m+3
  let q := D / 2^(n+4)
  have hp : 2^(n+4)=2^(n+2)*4 := by
    rw [show n+4=(n+2)+2 by omega, Nat.pow_add,
      show (2:Nat)^2=4 by decide]
  have hmod := Nat.mod_add_div D (2^(n+4))
  rw [h] at hmod
  have hD : D=2^(n+2)*(4*q+1) := by
    calc
      D = 2^(n+2)+2^(n+4)*q := hmod.symm
      _ = 2^(n+2)+(2^(n+2)*4)*q := by rw [hp]
      _ = 2^(n+2)*(4*q+1) := by
        rw [Nat.mul_add]
        ac_rfl
  change v2 D=n+2
  rw [hD]
  apply v2_pow_mul_odd
  omega

def candidateDepth (j m : Nat) : Nat :=
  v2 (j+3*m+3)

/-- One-candidate executable version of Agent19's all-natural depth guard. -/
def candidateAllowedBool (j m : Nat) : Bool :=
  let v := candidateDepth j m
  if 2≤v ∧ v≤2*m then
    decide (¬( (v-2)+4≤2*m+2 ∧
      (j+3*m+3)%2^((v-2)+4)=2^((v-2)+2) ∧
      (2*j+3)%8=(if (v-2)%2=0 then 7 else 3)))
  else true

theorem candidateAllowedBool_iff (j m : Nat) :
    candidateAllowedBool j m = true ↔ ∀ n, ¬gate n j m := by
  unfold candidateAllowedBool
  let v := candidateDepth j m
  change (if 2≤v ∧ v≤2*m then
    decide (¬( (v-2)+4≤2*m+2 ∧
      (j+3*m+3)%2^((v-2)+4)=2^((v-2)+2) ∧
      (2*j+3)%8=(if (v-2)%2=0 then 7 else 3)))
    else true) = true ↔ ∀ n, ¬gate n j m
  by_cases hv : 2≤v ∧ v≤2*m
  · simp only [if_pos hv, decide_eq_true_eq]
    constructor
    · intro h n hn
      rcases hn with ⟨hbound,hres,hpar⟩
      have hv2 := v2_of_older_residue j m n hres
      change v=n+2 at hv2
      have hnEq : n=v-2 := by omega
      subst n
      exact h ⟨by omega,hres,hpar⟩
    · intro h hcand
      exact (h (v-2)) hcand
  · simp only [if_neg hv, true_iff]
    intro n hn
    rcases hn with ⟨hbound,hres,hpar⟩
    have hv2 := v2_of_older_residue j m n hres
    change v=n+2 at hv2
    apply hv
    constructor
    · omega
    · omega

#print axioms v2_of_older_residue
#print axioms candidateAllowedBool_iff
end BB6.Agent11OlderGateFast
