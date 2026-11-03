import M8TraceCert
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 300000
set_option maxHeartbeats 0

namespace BB6.Agent1M8

/-- Finite low-parameter stopping family from the original Machine C
    normalization. This definition is used only for 0 <= m <= 8 here. -/
def lowGate (m : Nat) : Nat := 2^(2*m+3) - 3*m - 4

theorem low_gate_is_terminal (m : Nat) (hm : m <= 8) :
    BB6.Agent46.secNext (1, lowGate m) = none := by
  have hc : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨
            m=5 ∨ m=6 ∨ m=7 ∨ m=8 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h <;>
    subst m <;> decide

theorem low_gate_below_mass_cutoff (m : Nat) (hm : m <= 8) :
    1 + 2 * lowGate m < 1048525 := by
  have hc : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨
            m=5 ∨ m=6 ∨ m=7 ∨ m=8 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h <;>
    subst m <;> decide

/-- All nine low-parameter immediate stopping gates are excluded at every
    time on the genuine source-defined blank-origin section orbit.
    This does not decide the infinite family of remaining stop parameters. -/
theorem low_gates_0_through_8_unreachable (m : Nat) (hm : m <= 8) :
    ¬ ∃ n : Nat,
      BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) =
        some (1, lowGate m) := by
  exact all_terminal_below_rank_unreachable (1) (lowGate m)
    (low_gate_is_terminal m hm) (low_gate_below_mass_cutoff m hm)

#print axioms low_gate_is_terminal
#print axioms low_gate_below_mass_cutoff
#print axioms low_gates_0_through_8_unreachable

end BB6.Agent1M8
