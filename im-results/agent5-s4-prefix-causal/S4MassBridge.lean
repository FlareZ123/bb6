import S4MassDyadicPower
import Lean.Elab.Tactic.Omega

namespace S4Mass

/-- Exact dyadic-place weight shift under arbitrary stack concatenation. -/
theorem W_append (xs ys : List Nat) :
    W (xs ++ ys) = W xs + 2 ^ xs.length * W ys := by
  induction xs with
  | nil => simp [W]
  | cons a xs ih =>
    simp [W, ih, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc,
       Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    simp [Nat.mul_left_comm]

/-- For any nine-digit prefix whose first S4 gate is in the admissible
dyadic residue, and any sufficiently large prescribed suffix mass,
one can construct a synthetic stopping suffix with at most three digits
and *exactly that mass*. This theorem does not establish root reachability. -/
theorem synthetic_first_gate_with_mass (xs : List Nat) (m k : Nat)
    (hl : xs.length = 9)
    (hgate : W xs + 509 = 512 * k)
    (hm : 10 ≤ m) (hk : k ≤ m) :
    ∃ ys : List Nat, mass ys = m ∧ ys.length ≤ 3 ∧
      ∃ e : Nat, W (xs ++ ys) + 509 = 2 ^ e := by
  obtain ⟨e, ys, hmass, hpower, hlen⟩ :=
    exact_mass_power2_completion m k hm hk
  refine ⟨ys, hmass, hlen, 9 + e, ?_⟩
  have hw := W_append xs ys
  rw [hl] at hw
  simp at hw
  calc
    W (xs ++ ys) + 509 = 512 * (k + W ys) := by omega
    _ = 512 * 2 ^ e := by rw [show k + W ys = 2 ^ e by omega]
    _ = 2 ^ (9 + e) := by simp [Nat.pow_add]

#print axioms W_append
#print axioms synthetic_first_gate_with_mass

end S4Mass
