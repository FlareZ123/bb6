import SourceDirect
import Lean.Elab.Tactic.Omega

namespace BB6.Agent47Direct

/-- A sparse family of low-stop parameters with a large power-of-two divisor. -/
def lowIndex : Nat → Nat
  | 0 => 2
  | q+1 => 4*lowIndex q + 2

theorem index_power (q : Nat) :
    3*lowIndex q+2=2^(2*q+3) := by
  induction q with
  | zero => decide
  | succ q ih =>
      simp only [lowIndex]
      have he : 2*(q+1)+3=(2*q+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide] at *
      omega

theorem index_bound (q : Nat) : q+2 ≤ lowIndex q := by
  induction q with
  | zero => decide
  | succ q ih =>
      simp only [lowIndex]
      omega

def lowUnit (q : Nat) : Nat := 2^(2*(lowIndex q-q))-1

theorem lowUnit_bound (q : Nat) : 4 ≤ lowUnit q := by
  have hb := index_bound q
  have hp : 4 ≤ 2*(lowIndex q-q) := by omega
  have hpow : (2:Nat)^4 ≤ 2^(2*(lowIndex q-q)) :=
    Nat.pow_le_pow_right (by decide) hp
  dsimp [lowUnit]
  change 16 ≤ 2^(2*(lowIndex q-q)) at hpow
  omega

theorem low_gate_identity (q : Nat) :
    2^(2*lowIndex q+3)-(3*lowIndex q+4) =
      2^(2*q+3)*lowUnit q-2 := by
  have hb := index_bound q
  have hsplit : 2*lowIndex q+3=(2*q+3)+2*(lowIndex q-q) := by omega
  have hpow : 2^(2*lowIndex q+3)=
      2^(2*q+3)*2^(2*(lowIndex q-q)) := by rw [hsplit, Nat.pow_add]
  have hd : 3*lowIndex q+2=2^(2*q+3) := index_power q
  have hunit : 1 ≤ 2^(2*(lowIndex q-q)) := Nat.pow_pos (by decide)
  have hmul : 2^(2*q+3)*lowUnit q + 2^(2*q+3) = 2^(2*lowIndex q+3) := by
    rw [hpow]
    dsimp [lowUnit]
    have hk : 2^(2*(lowIndex q-q))-1+1=2^(2*(lowIndex q-q)) := by omega
    calc
      2^(2*q+3)*(2^(2*(lowIndex q-q))-1)+2^(2*q+3)
          = 2^(2*q+3)*((2^(2*(lowIndex q-q))-1)+1) := by simp only [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [hk]
  omega

/-- Every q gives a section path of length 2q+3 ending at a genuine
    Machine C low-family stop target; no blank-root claim is made. -/
theorem low_gate_unbounded_ancestry (q : Nat) :
    ∃ s, Chain BB6.Agent46.secNext (2*q+3) s
      (1, 2^(2*lowIndex q+3)-(3*lowIndex q+4)) := by
  obtain ⟨s,h⟩ := source_long_chain (2*q+3) (lowUnit q) 1
      (lowUnit_bound q)
  rw [low_gate_identity q]
  exact ⟨s,h⟩

#print axioms low_gate_unbounded_ancestry
end BB6.Agent47Direct
