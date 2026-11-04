import NoTarget
import ConeCore
namespace Agent22Special

/-- Source-connected exclusion of an infinite family from the actual blank
    even-section orbit. This family is NOT the halting power-of-two family. -/
theorem no_blank_even_reach_3pow (k : Nat) :
    ¬ SheepEven.EvenReach 10 (3*2^(4*k+2)) := by
  apply Agent22SheepCones.no_reach_without_incoming
  · have hp : (2:Nat)^2 ≤ 2^(4*k+2) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · intro x
    exact no_even_edge_to_3pow k x

#print axioms no_blank_even_reach_3pow
end Agent22Special
