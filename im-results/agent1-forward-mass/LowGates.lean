import ForwardStandalone
import Lean.Elab.Tactic.Omega

namespace ForwardLowGates

def lowGate (m : Nat) : Nat := 2^(2*m+3) - 3*m - 4

theorem lowGate_terminal_0_through_8 (m : Nat) (hm : m ≤ 8) :
    ForwardC.secNext (1, lowGate m) = none := by
  rw [← FuelBridge.next_correct]
  have hcases : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨
                m=5 ∨ m=6 ∨ m=7 ∨ m=8 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h <;>
    subst m <;> decide

theorem lowGate_mass_below_cutoff (m : Nat) (hm : m ≤ 8) :
    1+2*(lowGate m)<1048525 := by
  have hcases : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨
                m=5 ∨ m=6 ∨ m=7 ∨ m=8 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h <;>
    subst m <;> decide

/-- Nine low-gate arithmetic inputs excluded by one exact chunk certificate. -/
theorem lowGate_unreachable_0_through_8 (m : Nat) (hm : m ≤ 8) :
    ∀ n, ForwardMass.run ForwardC.secNext (5,1) n ≠ some (1,lowGate m) := by
  exact ForwardStandalone.model_all_small_terminal_unreachable (1,lowGate m)
    (lowGate_terminal_0_through_8 m hm) (lowGate_mass_below_cutoff m hm)

#print axioms lowGate_unreachable_0_through_8
end ForwardLowGates
