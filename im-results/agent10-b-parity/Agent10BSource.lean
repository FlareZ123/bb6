import BOneDim
import Agent10BParity

namespace BB6.Agent10B

/-- The local scalar map is definitionally identical to the source-certified Agent 18 map. -/
theorem G_eq_source (z : Nat) : G z = BB6.OneDim.G z := rfl

theorem iterG_eq_source (n z : Nat) : iterG n z = BB6.OneDim.iterG n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change iterG n (G z) = BB6.OneDim.iterG n (BB6.OneDim.G z)
    rw [G_eq_source]
    exact ih (BB6.OneDim.G z)

/-- No eventually periodic binary itinerary on the actual Agent 18 B scalar map. -/
theorem source_B_scalar_bits_aperiodic (n p : Nat) (hp : 0<p) :
    ¬ (∀ k : Nat,
      (BB6.OneDim.iterG (n+k) 0)%2 =
      (BB6.OneDim.iterG (n+k+p) 0)%2) := by
  intro h
  apply B_scalar_bits_aperiodic n p hp
  intro k
  rw [iterG_eq_source, iterG_eq_source]
  exact h k

#print axioms source_B_scalar_bits_aperiodic
end BB6.Agent10B
