import Std

namespace Agent8Potential

def potential (r a : Nat) : Nat := r * (r + 1) + 2 * (r - a)

theorem mul_identity (r : Nat) :
    r * (r + 1) + 2 * r + 2 = (r + 1) * (r + 2) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

theorem potential_step (r r' a a' : Nat)
    (ha : a ≤ r) (ha' : a' ≤ r')
    (h : r < r' ∨ (r = r' ∧ a' < a)) :
    potential r a + 2 ≤ potential r' a' := by
  rcases h with h | ⟨he, hd⟩
  · have hm : (r + 1) * (r + 2) ≤ r' * (r' + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hh := mul_identity r
    simp only [potential]
    omega
  · subst r'
    simp only [potential]
    omega

#print axioms potential_step
end Agent8Potential
