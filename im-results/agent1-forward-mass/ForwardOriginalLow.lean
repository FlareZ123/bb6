import ForwardOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent1ForwardLow

def lowGate (m : Nat) : Nat := 2^(2*m+3) - 3*m - 4

theorem source_low_gate_terminal (m : Nat) (hm : m ≤ 8) :
    BB6.Agent46.secNext (1,lowGate m) = none := by
  rw [← BB6.Agent1Forward.next_agrees]
  have hc : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨
            m=5 ∨ m=6 ∨ m=7 ∨ m=8 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h <;>
    subst m <;> decide

theorem source_low_gate_small (m : Nat) (hm : m ≤ 8) :
    1+2*(lowGate m)<1048525 := by
  have hc : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨
            m=5 ∨ m=6 ∨ m=7 ∨ m=8 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h <;>
    subst m <;> decide

/-- All nine finite low Machine C terminal targets, conditional on authentic
    source connection of the whole original first-return section map. -/
theorem source_low_gates_0_through_8 (m : Nat) (hm : m ≤ 8) :
    ∀ n, ForwardMass.run BB6.Agent46.secNext (5,1) n ≠ some (1,lowGate m) := by
  exact BB6.Agent1Forward.all_terminal_lower_mass_unreachable (1,lowGate m)
    (source_low_gate_terminal m hm) (source_low_gate_small m hm)

#print axioms source_low_gates_0_through_8
end BB6.Agent1ForwardLow
