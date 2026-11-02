import BTower

namespace BB6.Agent50
open BB6.BReduction

/-- A uniform affine upper envelope for the parity/payload transformation. -/
theorem F_payload_upper (p d : Nat) (hp : p ≤ 1) :
    2*((F (p,d)).2+12) ≤ 3*(d+12) := by
  simp only [F]
  omega

/-- Two-sided exponential envelope for the transducer payload. -/
theorem iterF_payload_upper (n p d : Nat) (hp : p ≤ 1) :
    2^n*((iterF n (p,d)).2+12) ≤ 3^n*(d+12) := by
  induction n generalizing p d with
  | zero => simp [iterF]
  | succ n ih =>
    have hf := F_payload_upper p d hp
    have hfa := Nat.mul_le_mul_left (3^n) hf
    have hbit : (F (p,d)).1 ≤ 1 := by simp [F]; omega
    have hi := ih (F (p,d)).1 (F (p,d)).2 hbit
    have hpair : ((F (p,d)).1,(F (p,d)).2) = F (p,d) := by
      cases F (p,d) <;> rfl
    rw [hpair] at hi
    have hia := Nat.mul_le_mul_left 2 hi
    calc
      2^(n+1)*((iterF (n+1) (p,d)).2+12) =
        2*(2^n*((iterF n (F (p,d))).2+12)) := by
          simp [iterF, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
      _ ≤ 2*(3^n*((F (p,d)).2+12)) := hia
      _ = 3^n*(2*((F (p,d)).2+12)) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 3^n*(3*(d+12)) := hfa
      _ = 3^(n+1)*(d+12) := by simp only [Nat.pow_succ]; ac_rfl

/-- The total reset recurrence has matching exponential upper envelope. -/
theorem reset_superexp_upper (n : Nat) :
    2^(resetA n)*resetA (n+1) + 15*2^(resetA n) ≤
      24*3^(resetA n) := by
  have h := iterF_payload_upper (resetA n) 0 0 (by omega)
  simp only [Nat.zero_add] at h
  calc
    2^(resetA n)*resetA (n+1) + 15*2^(resetA n) =
      2*(2^(resetA n)*((iterF (resetA n) (0,0)).2+12)) := by
        simp [resetA, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        omega
    _ ≤ 2*(3^(resetA n)*12) := Nat.mul_le_mul_left 2 h
    _ = 24*3^(resetA n) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      omega

#print axioms F_payload_upper
#print axioms iterF_payload_upper
#print axioms reset_superexp_upper
end BB6.Agent50
