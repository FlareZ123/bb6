import Lean
import Lean.Elab.Tactic.Omega
import HighDyadicGateDecisionFast

namespace BB6.Agent11LateDepthGate

open BB6.Agent11FastDepthGate

def stopK (j m : Nat) : Nat :=
  2^(2*m+2)*(j+3)-(j+3*m+5)

/-- The arbitrary-depth three-cone gate. It has no upper bound on r. -/
def gate (r j m : Nat) : Prop :=
  2≤r ∧ 3≤m ∧ m%4=(2*r+1)%4 ∧
  (stopK j m+2)%2^(r+2)=3*2^r ∧
  7*2^r≤stopK j m+2

instance (r j m : Nat) : Decidable (gate r j m) := by
  unfold gate
  infer_instance

def candidateDepth (j m : Nat) : Nat :=
  v2 (stopK j m+2)

/-- Direct candidate for the arbitrary-depth three-cone high obstruction. -/
def candidateAllowedBool (j m : Nat) : Bool :=
  let r := candidateDepth j m
  decide (2≤r ∧ 3≤m ∧ m%4=(2*r+1)%4 ∧
    (stopK j m+2)%2^(r+2)=3*2^r ∧
    7*2^r≤stopK j m+2)

theorem v2_of_late_residue (k r : Nat)
    (h : (k+2)%2^(r+2)=3*2^r) :
    v2 (k+2)=r := by
  let D := k+2
  let q := D / 2^(r+2)
  have hp : 2^(r+2) = 2^r*4 := by
    rw [Nat.pow_add, show (2:Nat)^2=4 by decide]
  have hmod := Nat.mod_add_div D (2^(r+2))
  rw [h] at hmod
  have hD : D = 2^r*(4*q+3) := by
    calc
      D = 3*2^r + 2^(r+2)*q := hmod.symm
      _ = 3*2^r + (2^r*4)*q := by rw [hp]
      _ = 2^r*(4*q+3) := by
        rw [Nat.mul_add]
        ac_rfl
  change v2 D = r
  rw [hD]
  apply v2_pow_mul_odd
  omega

/-- The residue has at most one possible inverse depth, and this Boolean
    checks exactly that candidate rather than scanning all natural r. -/
theorem candidateAllowedBool_iff (j m : Nat) :
    candidateAllowedBool j m = true ↔ ∃ r, gate r j m := by
  unfold candidateAllowedBool
  let r := candidateDepth j m
  change decide (2≤r ∧ 3≤m ∧ m%4=(2*r+1)%4 ∧
    (stopK j m+2)%2^(r+2)=3*2^r ∧
    7*2^r≤stopK j m+2) = true ↔ ∃ s, gate s j m
  constructor
  · intro h
    exact ⟨r, of_decide_eq_true h⟩
  · rintro ⟨s,hsmin,hm,hm4,hmod,hsize⟩
    have hv := v2_of_late_residue (stopK j m) s hmod
    change r=s at hv
    subst s
    exact decide_eq_true_eq.mpr ⟨hsmin,hm,hm4,hmod,hsize⟩

def allowedBool (j m : Nat) : Bool :=
  !(candidateAllowedBool j m)

theorem allowedBool_iff (j m : Nat) :
    allowedBool j m = true ↔ ∀ r, ¬gate r j m := by
  unfold allowedBool
  cases h : candidateAllowedBool j m with
  | false =>
      constructor
      · intro _
        intro r hr
        have hc := (candidateAllowedBool_iff j m).mpr ⟨r,hr⟩
        rw [h] at hc
        contradiction
      · intro _
        rfl
  | true =>
      constructor
      · intro hfalse
        cases hfalse
      · intro hall
        obtain ⟨r,hr⟩ := (candidateAllowedBool_iff j m).mp h
        exact (hall r hr).elim

def allowedDecidable (j m : Nat) :
    Decidable (∀ r, ¬gate r j m) :=
  if h : allowedBool j m = true then
    isTrue ((allowedBool_iff j m).mp h)
  else
    isFalse (fun hp => h ((allowedBool_iff j m).mpr hp))

#print axioms v2_of_late_residue
#print axioms candidateAllowedBool_iff
#print axioms allowedBool_iff
#print axioms allowedDecidable
end BB6.Agent11LateDepthGate
