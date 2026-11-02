import BDyadic
namespace BB6.OneDim

/-- Uniform balance identity on either constant-parity affine branch. -/
theorem G_balance_bit (bit z : Nat) (hb : bit ≤ 1) (hz : z%2=bit) :
    2*(G z+(if bit=0 then 8 else 15)) =
      3*(z+(if bit=0 then 8 else 15)) := by
  have hcase : bit=0 ∨ bit=1 := by omega
  rcases hcase with h | h
  · have hz0 : z%2=0 := by omega
    simpa [h] using G_balance_even z hz0
  · have hz1 : z%2=1 := by omega
    simpa [h] using G_balance_odd z hz1

/-- Finite prefix with a constant desired parity. -/
def samePrefix (bit : Nat) : Nat → Nat → Prop
  | 0, _ => True
  | n+1, z => z%2=bit ∧ samePrefix bit n (G z)

theorem samePrefix_iff (bit n z : Nat) :
    samePrefix bit n z ↔ ∀ i : Nat, i<n → (iterG i z)%2=bit := by
  induction n generalizing z with
  | zero => simp [samePrefix]
  | succ n ih =>
      constructor
      · rintro ⟨hz, hs⟩ i hi
        cases i with
        | zero => simpa [iterG] using hz
        | succ j =>
            have hj : j<n := by omega
            exact (ih (G z)).mp hs j hj
      · intro h
        constructor
        · exact h 0 (by omega)
        · apply (ih (G z)).mpr
          intro i hi
          exact h (i+1) (by omega)

end BB6.OneDim
