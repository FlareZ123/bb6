import Agent18BOneDim
import BParityRuns

namespace BB6.BParityRuns

theorem source_G (z : Nat) : G z = OneDim.G z := rfl

theorem source_iterG (n z : Nat) : iterG n z = OneDim.iterG n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      change iterG n (G z) = OneDim.iterG n (OneDim.G z)
      rw [source_G z]
      exact ih (OneDim.G z)

/-- Every Machine B scalar trajectory has a later step of the opposite parity. -/
theorem source_later_opposite (z n : Nat) :
    ∃ m : Nat, n < m ∧ (OneDim.iterG m z)%2 ≠ (OneDim.iterG n z)%2 := by
  obtain ⟨m,hm,hbit⟩ := later_opposite z n
  refine ⟨m,hm,?_⟩
  simpa only [source_iterG] using hbit

#print axioms source_later_opposite
end BB6.BParityRuns
