import P1ConeNoOne0

namespace BB6.Agent28
open BB6.P1Reduction

theorem no_one_5 (t q : Nat) :
    ∀ k, ¬GAncestor (89600*t + 88800*q + 89572) (139776*t + 138528*q + 139751) k 1 := by
  apply ancestor_one_exclusion _ _ 2
  · change ((139776*t + 138528*q + 139751) + (89600*t + 88800*q + 89572)/2 + 3)%8=4
    omega
  · change 4 < (139776*t + 138528*q + 139751) + (89600*t + 88800*q + 89572)/2 + 3
    omega

theorem no_one_6 (t q : Nat) :
    ∀ k, ¬GAncestor (44800*t + 44400*q + 44780) (184576*t + 182928*q + 184541) k 1 := by
  apply ancestor_one_exclusion _ _ 1
  · change ((184576*t + 182928*q + 184541) + (44800*t + 44400*q + 44780)/2 + 3)%4=2
    omega
  · change 2 < (184576*t + 182928*q + 184541) + (44800*t + 44400*q + 44780)/2 + 3
    omega

theorem no_one_7 (t q : Nat) :
    ∀ k, ¬GAncestor (22400*t + 22200*q + 22384) (206976*t + 205128*q + 206935) k 1 := by
  apply ancestor_one_exclusion _ _ 1
  · change ((206976*t + 205128*q + 206935) + (22400*t + 22200*q + 22384)/2 + 3)%4=2
    omega
  · change 2 < (206976*t + 205128*q + 206935) + (22400*t + 22200*q + 22384)/2 + 3
    omega

theorem no_one_8 (t q : Nat) :
    ∀ k, ¬GAncestor (137088*t + 135864*q + 137048) (92288*t + 91464*q + 92271) k 1 := by
  apply ancestor_one_exclusion _ _ 1
  · change ((92288*t + 91464*q + 92271) + (137088*t + 135864*q + 137048)/2 + 3)%4=2
    omega
  · change 2 < (92288*t + 91464*q + 92271) + (137088*t + 135864*q + 137048)/2 + 3
    omega

theorem no_one_9 (t q : Nat) :
    ∀ k, ¬GAncestor (200704*t + 198912*q + 200660) (28672*t + 28416*q + 28669) k 1 := by
  apply ancestor_one_exclusion _ _ 1
  · change ((28672*t + 28416*q + 28669) + (200704*t + 198912*q + 200660)/2 + 3)%4=2
    omega
  · change 2 < (28672*t + 28416*q + 28669) + (200704*t + 198912*q + 200660)/2 + 3
    omega

end BB6.Agent28
