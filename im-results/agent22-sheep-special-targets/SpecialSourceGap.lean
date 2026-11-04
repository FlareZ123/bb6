import Std

namespace Agent22Special

/-- Exponential domination from the first legal positive 2-adic valuation. -/
theorem special_valuation_gap (b : Nat) (hb : 1 ≤ b) : b + 3 < 3 * 2^b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  suffices h : ∀ n : Nat, n + 4 < 3 * 2^(n+1) by
    simpa [Nat.succ_eq_add_one] using h n
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-- No positive-valuation special cofactor-three source reaches another
    3-times-a-power-of-two as an immediate ordinary-section successor. -/
theorem no_special_source (a b : Nat) (hb : 1 ≤ b) :
    3*2^a ≠ 3*2^b+b+3 := by
  intro heq
  have hgap := special_valuation_gap b hb
  by_cases hab : a ≤ b
  · have hpow : (2:Nat)^a ≤ 2^b := Nat.pow_le_pow_right (by decide) hab
    omega
  · have hab' : b+1 ≤ a := by omega
    have hpow : (2:Nat)^(b+1) ≤ 2^a := Nat.pow_le_pow_right (by decide) hab'
    rw [Nat.pow_succ] at hpow
    omega

/-- A target divisible by 3 cannot be the endpoint of a positive-length
    odd block, whose endpoint is congruent to 1 modulo 3. -/
theorem triple_target_odd_block_zero (a h u : Nat)
    (heq : 3*2^a = 1+3^h*u) : h=0 := by
  cases h with
  | zero => rfl
  | succ h =>
    have hm := congrArg (fun n : Nat => n%3) heq
    simp [Nat.pow_succ, Nat.mul_mod, Nat.add_mod] at hm

#print axioms no_special_source
#print axioms triple_target_odd_block_zero
end Agent22Special
