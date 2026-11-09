import SweepEvenDeficit
import SweepAddress

namespace CascadeFastReturn
open CascadeBitSweep

/-- A reset that remains in the same dyadic sweep level is necessarily
    even and exactly halves that level's upper deficit. -/
theorem same_address_forces_half_deficit (h u : Nat)
    (ho : bitOutcome h=some u)
    (hsame : firstFailIndex h=firstFailIndex u) :
    (h+firstFailIndex h)%2=0 ∧
      deficitAt (firstFailIndex h) h = 2*deficitAt (firstFailIndex h) u := by
  by_cases heven : (h+firstFailIndex h)%2=0
  · exact ⟨heven, bitOutcome_even_deficit_halves h (firstFailIndex h) u rfl heven ho⟩
  · have hodd : (h+firstFailIndex h)%2=1 := by omega
    have hp := bitOutcome_odd_address_increases h u ho hodd
    omega

#print axioms same_address_forces_half_deficit
end CascadeFastReturn
