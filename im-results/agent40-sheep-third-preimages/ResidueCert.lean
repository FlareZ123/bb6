import Std

/-! Lean 4.36.0-rc2 certified finite-modulus gates for Sheep inverse depth three.
The general residue-gap and interval lemmas are proved in README.md, not this file. -/

namespace SheepThird

private theorem period216 (m r q : Nat) (hp : 2^216 % m = 1) :
    2^(r + 216*q) % m = 2^r % m := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
  rw [Nat.pow_mod (2^216) q m, hp]
  simp

private theorem periodNe (m r k q target : Nat)
    (hp : 2^216 % m = 1) (hb : 2^(r+k) % m ≠ target) :
    2^(r+216*q+k) % m ≠ target := by
  rw [show r+216*q+k = (r+k)+216*q by omega, period216 m (r+k) q hp]
  exact hb

private theorem period10 (m r q : Nat) (hp : 2^10 % m = 1) :
    2^(r + 10*q) % m = 2^r % m := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
  rw [Nat.pow_mod (2^10) q m, hp]
  simp

theorem oddPow11 (n : Nat) : 2^(2*n+1) % 11 ≠ 9 := by
  have he : 2*n+1 = (2*(n%5)+1)+10*(n/5) := by omega
  rw [he, period10 11 (2*(n%5)+1) (n/5) (by decide)]
  have hl : n%5 < 5 := Nat.mod_lt n (by decide)
  have hcases : n%5 = 0 ∨ n%5 = 1 ∨ n%5 = 2 ∨ n%5 = 3 ∨ n%5 = 4 := by omega
  rcases hcases with h | h | h | h | h <;> simp [h] <;> decide

theorem evenPow11 (n : Nat) : 2^(2*n) % 11 ≠ 8 := by
  have he : 2*n = (2*(n%5))+10*(n/5) := by omega
  rw [he, period10 11 (2*(n%5)) (n/5) (by decide)]
  have hl : n%5 < 5 := Nat.mod_lt n (by decide)
  have hcases : n%5 = 0 ∨ n%5 = 1 ∨ n%5 = 2 ∨ n%5 = 3 ∨ n%5 = 4 := by omega
  rcases hcases with h | h | h | h | h <;> simp [h] <;> decide

def smallGateBarriers (j : Nat) : Prop :=
    2^(j+1) % 5 ≠ 1 ∧
    2^(j+2) % 5 ≠ 1 ∧
    2^(j+2) % 27 ≠ 7 ∧
    2^(j+2) % 17 ≠ 13 ∧
    2^(j+3) % 27 ≠ 8 ∧
    2^(j+3) % 5 ≠ 4 ∧
    2^(j+3) % 81 ≠ 17 ∧
    2^(j+3) % 17 ≠ 1 ∧
    2^(j+3) % 5 ≠ 1

theorem residue24 (q : Nat) : smallGateBarriers (24+216*q) := by
  unfold smallGateBarriers
  exact ⟨
    periodNe 5 24 1 q 1 (by decide) (by decide),
    periodNe 5 24 2 q 1 (by decide) (by decide),
    periodNe 27 24 2 q 7 (by decide) (by decide),
    periodNe 17 24 2 q 13 (by decide) (by decide),
    periodNe 27 24 3 q 8 (by decide) (by decide),
    periodNe 5 24 3 q 4 (by decide) (by decide),
    periodNe 81 24 3 q 17 (by decide) (by decide),
    periodNe 17 24 3 q 1 (by decide) (by decide),
    periodNe 5 24 3 q 1 (by decide) (by decide)
  ⟩

theorem residue48 (q : Nat) : smallGateBarriers (48+216*q) := by
  unfold smallGateBarriers
  exact ⟨
    periodNe 5 48 1 q 1 (by decide) (by decide),
    periodNe 5 48 2 q 1 (by decide) (by decide),
    periodNe 27 48 2 q 7 (by decide) (by decide),
    periodNe 17 48 2 q 13 (by decide) (by decide),
    periodNe 27 48 3 q 8 (by decide) (by decide),
    periodNe 5 48 3 q 4 (by decide) (by decide),
    periodNe 81 48 3 q 17 (by decide) (by decide),
    periodNe 17 48 3 q 1 (by decide) (by decide),
    periodNe 5 48 3 q 1 (by decide) (by decide)
  ⟩

theorem residue96 (q : Nat) : smallGateBarriers (96+216*q) := by
  unfold smallGateBarriers
  exact ⟨
    periodNe 5 96 1 q 1 (by decide) (by decide),
    periodNe 5 96 2 q 1 (by decide) (by decide),
    periodNe 27 96 2 q 7 (by decide) (by decide),
    periodNe 17 96 2 q 13 (by decide) (by decide),
    periodNe 27 96 3 q 8 (by decide) (by decide),
    periodNe 5 96 3 q 4 (by decide) (by decide),
    periodNe 81 96 3 q 17 (by decide) (by decide),
    periodNe 17 96 3 q 1 (by decide) (by decide),
    periodNe 5 96 3 q 1 (by decide) (by decide)
  ⟩

theorem residue120 (q : Nat) : smallGateBarriers (120+216*q) := by
  unfold smallGateBarriers
  exact ⟨
    periodNe 5 120 1 q 1 (by decide) (by decide),
    periodNe 5 120 2 q 1 (by decide) (by decide),
    periodNe 27 120 2 q 7 (by decide) (by decide),
    periodNe 17 120 2 q 13 (by decide) (by decide),
    periodNe 27 120 3 q 8 (by decide) (by decide),
    periodNe 5 120 3 q 4 (by decide) (by decide),
    periodNe 81 120 3 q 17 (by decide) (by decide),
    periodNe 17 120 3 q 1 (by decide) (by decide),
    periodNe 5 120 3 q 1 (by decide) (by decide)
  ⟩

theorem residue168 (q : Nat) : smallGateBarriers (168+216*q) := by
  unfold smallGateBarriers
  exact ⟨
    periodNe 5 168 1 q 1 (by decide) (by decide),
    periodNe 5 168 2 q 1 (by decide) (by decide),
    periodNe 27 168 2 q 7 (by decide) (by decide),
    periodNe 17 168 2 q 13 (by decide) (by decide),
    periodNe 27 168 3 q 8 (by decide) (by decide),
    periodNe 5 168 3 q 4 (by decide) (by decide),
    periodNe 81 168 3 q 17 (by decide) (by decide),
    periodNe 17 168 3 q 1 (by decide) (by decide),
    periodNe 5 168 3 q 1 (by decide) (by decide)
  ⟩

theorem smallGates (j : Nat)
    (hj : j % 216 = 24 ∨ j % 216 = 48 ∨ j % 216 = 96 ∨
          j % 216 = 120 ∨ j % 216 = 168) : smallGateBarriers j := by
  rcases hj with h | h | h | h | h
  · have eq : j = 24+216*(j/216) := by omega
    rw [eq]
    exact residue24 (j/216)
  · have eq : j = 48+216*(j/216) := by omega
    rw [eq]
    exact residue48 (j/216)
  · have eq : j = 96+216*(j/216) := by omega
    rw [eq]
    exact residue96 (j/216)
  · have eq : j = 120+216*(j/216) := by omega
    rw [eq]
    exact residue120 (j/216)
  · have eq : j = 168+216*(j/216) := by omega
    rw [eq]
    exact residue168 (j/216)

#print axioms smallGates
#print axioms oddPow11
#print axioms evenPow11
end SheepThird
