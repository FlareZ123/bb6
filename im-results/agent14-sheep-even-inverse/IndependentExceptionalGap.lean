import Std

namespace SheepIndependentGap

/-- A single checked exponential-versus-linear inequality controls every
larger exponent. No quantified search bound is introduced. -/
theorem gap_all (D L C t₀ : Nat) (ht₀ : 1 ≤ t₀)
    (h₀ : D*t₀ + C < L*2^t₀) :
    ∀ t : Nat, t₀ ≤ t → D*t + C < L*2^t := by
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction k with
  | zero => simpa using h₀
  | succ k ih =>
      have hprev : D * (t₀+k) + C < L*2^(t₀+k) := by simpa using ih
      have hmul : D ≤ D*(t₀+k)+C := by
        have hle : 1 ≤ t₀+k := by omega
        have hmul' := Nat.mul_le_mul_left D hle
        omega
      have hp : L*2^(t₀+(k+1)) = (L*2^(t₀+k))*2 := by
        rw [show t₀+(k+1)=t₀+k+1 by omega, Nat.pow_succ, Nat.mul_assoc]
      have hl : D*(t₀+(k+1))+C = (D*(t₀+k)+C)+D := by
        simp only [Nat.add_assoc, Nat.mul_add, Nat.mul_one]
        omega
      rw [hp,hl]
      omega

/-- Exact source-agnostic exceptional-power gap: once the coefficient
of 2^a lies strictly between consecutive powers of two, a single
base-exponent inequality forbids *all* exceptional parents at all
later target exponents and all source valuations a. -/
theorem no_special_equal (A D C e L t₀ : Nat)
    (hlo : 2^e < A) (hsum : A + L = 2^(e+1))
    (ht₀ : 1 ≤ t₀) (hbase : D*t₀+C < L*2^t₀) :
    ∀ t : Nat, t₀ ≤ t → ∀ a : Nat,
      A*2^a + D*a + C ≠ 2^(t+e+1) := by
  intro t ht a heq
  have hgap := gap_all D L C t₀ ht₀ hbase t ht
  by_cases ha : a ≤ t
  · have hpow : 2^a ≤ 2^t := Nat.pow_le_pow_right (by decide) ha
    have hA : A*2^a ≤ A*2^t := Nat.mul_le_mul_left A hpow
    have hD : D*a ≤ D*t := Nat.mul_le_mul_left D ha
    have htarget : 2^(t+e+1) = A*2^t+L*2^t := by
      rw [show t+e+1=e+1+t by omega, Nat.pow_add, ← hsum, Nat.add_mul]
    omega
  · have hb : t+1 ≤ a := by omega
    have hpow : 2^(t+1) ≤ 2^a := Nat.pow_le_pow_right (by decide) hb
    have hA : A*2^(t+1) ≤ A*2^a := Nat.mul_le_mul_left A hpow
    have hStrict : 2^e*2^(t+1) < A*2^(t+1) :=
      Nat.mul_lt_mul_of_pos_right hlo (Nat.pow_pos (by decide))
    have htarget : 2^(t+e+1) = 2^e*2^(t+1) := by
      rw [show t+e+1=e+(t+1) by omega, Nat.pow_add]
    omega

#print axioms gap_all
#print axioms no_special_equal
end SheepIndependentGap
