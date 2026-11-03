import CoreFamily
namespace Agent9LiteralShieldCounter
open Agent9Val
open Agent9CoreCounter

def initial : Nat := 3^4 * Agent9CoreCounter.u

/-- Literal q < 3^c fails as an all-time S-survival certificate. -/
theorem initial_below : initial < 3^67 := by decide

theorem reach_bad_core : steps 4 (some (initial,67)) = some (Agent9CoreCounter.q,63) := by
  have hh := zero_prefix 4 Agent9CoreCounter.u 67 4 (by omega) (by omega)
  have hq := (Agent9CoreCounter.core_below_exponential).1
  simpa [initial,hq] using hh

theorem first_literal_exit : steps 73 (some (initial,67))=none := by
  change steps (4+69) (some (initial,67))=none
  rw [steps_add,reach_bad_core]
  exact Agent9CoreCounter.exact_exit

theorem no_earlier_literal_exit (k : Nat) (hk : k <73) :
    ∃s, steps k (some (initial,67))=some s := by
  by_cases hsmall : k<4
  · refine ⟨(4^k*(3^(4-k)*Agent9CoreCounter.u),67-k),?_⟩
    simpa [initial] using zero_prefix 4 Agent9CoreCounter.u 67 k (by omega) (by omega)
  · have he : k=4+(k-4) := by omega
    rw [he,steps_add,reach_bad_core]
    exact Agent9CoreCounter.no_earlier_exit (k-4) (by omega)

#print axioms initial_below
#print axioms first_literal_exit
#print axioms no_earlier_literal_exit
end Agent9LiteralShieldCounter
