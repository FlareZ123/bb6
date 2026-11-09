import S4MassBridge
import S4Octet
import Lean.Elab.Tactic.Omega

namespace S4Mass

/-- The elementary digit-stack weight in the mass theorem is definitionally
compatible with the original-source S4 power-gate weight. -/
theorem W_eq_original (xs : List Nat) : W xs = S4Power.W xs := by
  induction xs with
  | nil => rfl
  | cons b ys ih => simp [W, S4Power.W, ih]

/-- Every length-nine S4 projected prefix exposing the first G(509)
power-gate residue has an exact-mass synthetic completion which *actually*
fails the original source S4Octet.G operation. This is an obstruction to
mass-only root nonhalting arguments, not an authentic-root halt witness. -/
theorem synthetic_original_first_gate (xs : List Nat) (m k : Nat)
    (hl : xs.length = 9)
    (hgate : W xs + 509 = 512 * k)
    (hm : 10 ≤ m) (hk : k ≤ m) :
    ∃ ys : List Nat, mass ys = m ∧ ys.length ≤ 3 ∧
      S4Octet.G 509 (xs ++ ys) = none := by
  obtain ⟨ys, hmass, hlen, e, he⟩ :=
    synthetic_first_gate_with_mass xs m k hl hgate hm hk
  have hw : S4Power.W (xs ++ ys) + 509 = 2 ^ e := by
    rw [← W_eq_original]
    exact he
  have hpow : S4Power.Pow2 (S4Power.W (xs ++ ys) + 509) := ⟨e, hw⟩
  refine ⟨ys, hmass, hlen, ?_⟩
  exact (S4Octet.G_none_iff_power 509 (xs ++ ys) (by omega)).mpr hpow

#print axioms W_eq_original
#print axioms synthetic_original_first_gate

end S4Mass
